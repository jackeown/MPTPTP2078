%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0927+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gFAAi4gQCs

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:44 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  404 (1078 expanded)
%              Number of leaves         :   36 ( 362 expanded)
%              Depth                    :   70
%              Number of atoms          : 5597 (16095 expanded)
%              Number of equality atoms :  931 (1400 expanded)
%              Maximal formula depth    :   32 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t87_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) )
     => ! [F: $i] :
          ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) )
         => ! [G: $i] :
              ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) )
             => ! [H: $i] :
                  ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) )
                 => ! [I: $i] :
                      ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
                     => ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
                       => ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E )
                          & ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F )
                          & ( r2_hidden @ ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G )
                          & ( r2_hidden @ ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) )
       => ! [F: $i] :
            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) )
                   => ! [I: $i] :
                        ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
                       => ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
                         => ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E )
                            & ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F )
                            & ( r2_hidden @ ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G )
                            & ( r2_hidden @ ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ~ ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('2',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ( X29 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('8',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( sk_B @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k10_mcart_1 @ X0 @ X1 @ X2 @ X3 @ X4 ) @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( m1_subset_1 @ ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( sk_B @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('17',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ X21 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('19',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(dt_k8_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k8_mcart_1 @ X10 @ X11 @ X12 @ X13 @ X14 ) @ X10 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_mcart_1])).

thf('21',plain,(
    m1_subset_1 @ ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_E ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( r2_hidden @ ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_E ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('25',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t86_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ( E != k1_xboole_0 )
        & ( F != k1_xboole_0 )
        & ( G != k1_xboole_0 )
        & ( H != k1_xboole_0 )
        & ? [I: $i] :
            ( ? [J: $i] :
                ( ~ ( ( ( k8_mcart_1 @ A @ B @ C @ D @ I )
                      = ( k8_mcart_1 @ E @ F @ G @ H @ J ) )
                    & ( ( k9_mcart_1 @ A @ B @ C @ D @ I )
                      = ( k9_mcart_1 @ E @ F @ G @ H @ J ) )
                    & ( ( k10_mcart_1 @ A @ B @ C @ D @ I )
                      = ( k10_mcart_1 @ E @ F @ G @ H @ J ) )
                    & ( ( k11_mcart_1 @ A @ B @ C @ D @ I )
                      = ( k11_mcart_1 @ E @ F @ G @ H @ J ) ) )
                & ( I = J )
                & ( m1_subset_1 @ J @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) )
            & ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) )).

thf('26',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X45 != X43 )
      | ( ( k8_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X45 )
        = ( k8_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t86_mcart_1])).

thf('27',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( ( k8_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X43 )
        = ( k8_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X42 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('29',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('30',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('31',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('34',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('35',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('36',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X44 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( ( k8_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X43 )
        = ( k8_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X42 = o_0_0_xboole_0 )
      | ( X41 = o_0_0_xboole_0 )
      | ( X40 = o_0_0_xboole_0 )
      | ( X39 = o_0_0_xboole_0 )
      | ( X38 = o_0_0_xboole_0 )
      | ( X37 = o_0_0_xboole_0 )
      | ( X36 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31','32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( X1 = o_0_0_xboole_0 )
      | ( X2 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 ) )
      | ( ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
        = ( k8_mcart_1 @ X0 @ X1 @ X2 @ X3 @ sk_I ) )
      | ( X3 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,
    ( ( sk_H = o_0_0_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( r2_hidden @ ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_E ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('42',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(dt_k9_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k9_mcart_1 @ X15 @ X16 @ X17 @ X18 @ X19 ) @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_mcart_1])).

thf('44',plain,(
    m1_subset_1 @ ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_F ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( r2_hidden @ ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k10_mcart_1 @ X0 @ X1 @ X2 @ X3 @ X4 ) @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_mcart_1])).

thf('49',plain,(
    m1_subset_1 @ ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_G ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ( r2_hidden @ ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(dt_k11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ) )).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k11_mcart_1 @ X5 @ X6 @ X7 @ X8 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_mcart_1])).

thf('54',plain,(
    m1_subset_1 @ ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_H )
    | ( r2_hidden @ ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_H )
    | ( r2_hidden @ ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('58',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('59',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X45 != X43 )
      | ( ( k11_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X45 )
        = ( k11_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t86_mcart_1])).

thf('61',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( ( k11_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X43 )
        = ( k11_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X42 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('63',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('64',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('65',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('66',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('67',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('68',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('69',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('70',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X44 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( ( k11_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X43 )
        = ( k11_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X42 = o_0_0_xboole_0 )
      | ( X41 = o_0_0_xboole_0 )
      | ( X40 = o_0_0_xboole_0 )
      | ( X39 = o_0_0_xboole_0 )
      | ( X38 = o_0_0_xboole_0 )
      | ( X37 = o_0_0_xboole_0 )
      | ( X36 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( X1 = o_0_0_xboole_0 )
      | ( X2 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 ) )
      | ( ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
        = ( k11_mcart_1 @ X0 @ X1 @ X2 @ X3 @ sk_I ) )
      | ( X3 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','70'])).

thf('72',plain,
    ( ( sk_H = o_0_0_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,
    ( ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['39'])).

thf('74',plain,
    ( ( ~ ( r2_hidden @ ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_H )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( v1_xboole_0 @ sk_H )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['57','74'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('76',plain,(
    ! [X33: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('77',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('78',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('82',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_C = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('85',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_C = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( v1_xboole_0 @ sk_H )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['56','86'])).

thf('88',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('89',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( v1_xboole_0 @ sk_G )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['51','96'])).

thf('98',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('99',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( v1_xboole_0 @ sk_F )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['46','106'])).

thf('108',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('109',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( v1_xboole_0 @ sk_E )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['41','116'])).

thf('118',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('119',plain,
    ( ( ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('122',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ o_0_0_xboole_0 ) )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('124',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('125',plain,
    ( ( ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('127',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ o_0_0_xboole_0 @ sk_H ) )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ( X27 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('129',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('131',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('132',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ o_0_0_xboole_0 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('134',plain,
    ( ( ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['127','132','133'])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('136',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ o_0_0_xboole_0 @ sk_G @ sk_H ) )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ( X26 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('138',plain,(
    ! [X25: $i,X27: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X25 @ k1_xboole_0 @ X27 @ X29 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('140',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('141',plain,(
    ! [X25: $i,X27: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X25 @ o_0_0_xboole_0 @ X27 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('143',plain,
    ( ( sk_E = o_0_0_xboole_0 )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['136','141','142'])).

thf('144',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('145',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ o_0_0_xboole_0 @ sk_F @ sk_G @ sk_H ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ( X25 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('147',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X26 @ X27 @ X29 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('149',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('150',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ o_0_0_xboole_0 @ X26 @ X27 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('152',plain,(
    r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ),
    inference(demod,[status(thm)],['145','150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('157',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ( r2_hidden @ ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('158',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('159',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X45 != X43 )
      | ( ( k10_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X45 )
        = ( k10_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t86_mcart_1])).

thf('161',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( ( k10_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X43 )
        = ( k10_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X42 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('163',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('164',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('165',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('166',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('167',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('168',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('169',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('170',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X44 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( ( k10_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X43 )
        = ( k10_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X42 = o_0_0_xboole_0 )
      | ( X41 = o_0_0_xboole_0 )
      | ( X40 = o_0_0_xboole_0 )
      | ( X39 = o_0_0_xboole_0 )
      | ( X38 = o_0_0_xboole_0 )
      | ( X37 = o_0_0_xboole_0 )
      | ( X36 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['161','162','163','164','165','166','167','168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( X1 = o_0_0_xboole_0 )
      | ( X2 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 ) )
      | ( ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
        = ( k10_mcart_1 @ X0 @ X1 @ X2 @ X3 @ sk_I ) )
      | ( X3 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['159','170'])).

thf('172',plain,
    ( ( sk_H = o_0_0_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['158','171'])).

thf('173',plain,
    ( ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(split,[status(esa)],['39'])).

thf('174',plain,
    ( ( ~ ( r2_hidden @ ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_G )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( ( v1_xboole_0 @ sk_G )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['157','174'])).

thf('176',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('177',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('180',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_C = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('182',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_C = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( ( v1_xboole_0 @ sk_H )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['156','182'])).

thf('184',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('185',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('188',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('190',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( v1_xboole_0 @ sk_G )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['155','190'])).

thf('192',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('193',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('196',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('198',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,
    ( ( ( v1_xboole_0 @ sk_F )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['154','198'])).

thf('200',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('201',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('204',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('206',plain,
    ( ! [X0: $i] :
        ( ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,
    ( ( ( v1_xboole_0 @ sk_E )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['153','206'])).

thf('208',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('209',plain,
    ( ( ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('212',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ o_0_0_xboole_0 ) )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('214',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('215',plain,
    ( ( ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('217',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ o_0_0_xboole_0 @ sk_H ) )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ o_0_0_xboole_0 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('219',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('220',plain,
    ( ( ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('222',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ o_0_0_xboole_0 @ sk_G @ sk_H ) )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X25: $i,X27: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X25 @ o_0_0_xboole_0 @ X27 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('224',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('225',plain,
    ( ( sk_E = o_0_0_xboole_0 )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('227',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ o_0_0_xboole_0 @ sk_F @ sk_G @ sk_H ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ o_0_0_xboole_0 @ X26 @ X27 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('229',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('230',plain,(
    r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ),
    inference(demod,[status(thm)],['227','228','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('232',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('233',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('234',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k10_mcart_1 @ X2 @ X1 @ X0 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('235',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( r2_hidden @ ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('236',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('237',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X45 != X43 )
      | ( ( k9_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X45 )
        = ( k9_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t86_mcart_1])).

thf('239',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( ( k9_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X43 )
        = ( k9_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X42 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('241',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('242',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('243',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('244',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('245',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('246',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('247',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('248',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X44 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ( ( k9_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X43 )
        = ( k9_mcart_1 @ X40 @ X41 @ X42 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 ) )
      | ( X42 = o_0_0_xboole_0 )
      | ( X41 = o_0_0_xboole_0 )
      | ( X40 = o_0_0_xboole_0 )
      | ( X39 = o_0_0_xboole_0 )
      | ( X38 = o_0_0_xboole_0 )
      | ( X37 = o_0_0_xboole_0 )
      | ( X36 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['239','240','241','242','243','244','245','246','247'])).

thf('249',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( X1 = o_0_0_xboole_0 )
      | ( X2 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 ) )
      | ( ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
        = ( k9_mcart_1 @ X0 @ X1 @ X2 @ X3 @ sk_I ) )
      | ( X3 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['237','248'])).

thf('250',plain,
    ( ( sk_H = o_0_0_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['236','249'])).

thf('251',plain,
    ( ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(split,[status(esa)],['39'])).

thf('252',plain,
    ( ( ~ ( r2_hidden @ ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_F )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,
    ( ( ( v1_xboole_0 @ sk_F )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['235','252'])).

thf('254',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('255',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('258',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_C = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('260',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_C = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,
    ( ( ( v1_xboole_0 @ sk_H )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['234','260'])).

thf('262',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('263',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('266',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('268',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,
    ( ( ( v1_xboole_0 @ sk_G )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['233','268'])).

thf('270',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('271',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('274',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('276',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['274','275'])).

thf('277',plain,
    ( ( ( v1_xboole_0 @ sk_F )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['232','276'])).

thf('278',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('279',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('282',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('284',plain,
    ( ! [X0: $i] :
        ( ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ( sk_G = o_0_0_xboole_0 )
        | ( sk_H = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('285',plain,
    ( ( ( v1_xboole_0 @ sk_E )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['231','284'])).

thf('286',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('287',plain,
    ( ( ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,
    ( ( ( sk_H = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(simplify,[status(thm)],['287'])).

thf('289',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('290',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ o_0_0_xboole_0 ) )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('292',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('293',plain,
    ( ( ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['290','291','292'])).

thf('294',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('295',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ o_0_0_xboole_0 @ sk_H ) )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ o_0_0_xboole_0 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('297',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('298',plain,
    ( ( ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('299',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('300',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ o_0_0_xboole_0 @ sk_G @ sk_H ) )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['298','299'])).

thf('301',plain,(
    ! [X25: $i,X27: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X25 @ o_0_0_xboole_0 @ X27 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('302',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('303',plain,
    ( ( sk_E = o_0_0_xboole_0 )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['300','301','302'])).

thf('304',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('305',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ o_0_0_xboole_0 @ sk_F @ sk_G @ sk_H ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ o_0_0_xboole_0 @ X26 @ X27 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('307',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('308',plain,(
    r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ),
    inference(demod,[status(thm)],['305','306','307'])).

thf('309',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['39'])).

thf('310',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['152','230','308','309'])).

thf('311',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['40','310'])).

thf('312',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_E )
    | ( sk_A = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_H = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','311'])).

thf('313',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( sk_H = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','312'])).

thf('314',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('315',plain,
    ( ( sk_A = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_H = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['313','314'])).

thf('316',plain,
    ( ( sk_H = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('318',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('320',plain,(
    ! [X0: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference(demod,[status(thm)],['318','319'])).

thf('321',plain,
    ( ( v1_xboole_0 @ sk_H )
    | ( sk_H = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','320'])).

thf('322',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('323',plain,
    ( ( sk_A = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_H = o_0_0_xboole_0 )
    | ( sk_H = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['321','322'])).

thf('324',plain,
    ( ( sk_H = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['323'])).

thf('325',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('326',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['324','325'])).

thf('327',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('328',plain,(
    ! [X0: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('329',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ( sk_H = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','328'])).

thf('330',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('331',plain,
    ( ( sk_A = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_H = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,
    ( ( sk_H = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['331'])).

thf('333',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('334',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['332','333'])).

thf('335',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('336',plain,(
    ! [X0: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('337',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( sk_H = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','336'])).

thf('338',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('339',plain,
    ( ( sk_A = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_H = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['337','338'])).

thf('340',plain,
    ( ( sk_H = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['339'])).

thf('341',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('342',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['340','341'])).

thf('343',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('344',plain,(
    ! [X0: $i] :
      ( ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_G = o_0_0_xboole_0 )
      | ( sk_H = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['342','343'])).

thf('345',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( sk_H = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','344'])).

thf('346',plain,(
    ! [X33: $i] :
      ( ( X33 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('347',plain,
    ( ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_H = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['345','346'])).

thf('348',plain,
    ( ( sk_H = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['347'])).

thf('349',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('350',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ o_0_0_xboole_0 ) )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['348','349'])).

thf('351',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('352',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('353',plain,
    ( ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_G = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['350','351','352'])).

thf('354',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('355',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ o_0_0_xboole_0 @ sk_H ) )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['353','354'])).

thf('356',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ o_0_0_xboole_0 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('357',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('358',plain,
    ( ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['355','356','357'])).

thf('359',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('360',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ o_0_0_xboole_0 @ sk_G @ sk_H ) )
    | ( sk_E = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['358','359'])).

thf('361',plain,(
    ! [X25: $i,X27: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X25 @ o_0_0_xboole_0 @ X27 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('362',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('363',plain,(
    sk_E = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362'])).

thf('364',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ o_0_0_xboole_0 @ X26 @ X27 @ X29 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('365',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('366',plain,(
    $false ),
    inference(demod,[status(thm)],['2','363','364','365'])).


%------------------------------------------------------------------------------
