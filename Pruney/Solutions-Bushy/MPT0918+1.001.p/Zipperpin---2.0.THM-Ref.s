%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0918+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ioaCrqrdlH

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 197 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          : 1694 (6462 expanded)
%              Number of equality atoms :  232 ( 968 expanded)
%              Maximal formula depth    :   28 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_I_4_type,type,(
    sk_I_4: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_4_type,type,(
    sk_H_4: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_4_type,type,(
    sk_G_4: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(t78_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ( D != k1_xboole_0 )
          & ? [F: $i,G: $i,H: $i,I: $i] :
              ( ~ ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                    = F )
                  & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                    = G )
                  & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                    = H )
                  & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                    = I ) )
              & ( E
                = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
       => ~ ( ( A != k1_xboole_0 )
            & ( B != k1_xboole_0 )
            & ( C != k1_xboole_0 )
            & ( D != k1_xboole_0 )
            & ? [F: $i,G: $i,H: $i,I: $i] :
                ( ~ ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                      = F )
                    & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                      = G )
                    & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                      = H )
                    & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                      = I ) )
                & ( E
                  = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( F
                      = ( k9_mcart_1 @ A @ B @ C @ D @ E ) )
                  <=> ! [G: $i,H: $i,I: $i,J: $i] :
                        ( ( E
                          = ( k4_mcart_1 @ G @ H @ I @ J ) )
                       => ( F = H ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X33 @ X31 )
      | ( X33
       != ( k9_mcart_1 @ X30 @ X31 @ X32 @ X35 @ X34 ) )
      | ( X33 = X36 )
      | ( X34
       != ( k4_mcart_1 @ X37 @ X36 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X35 ) )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d9_mcart_1])).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X37 @ X36 @ X38 @ X39 ) @ ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X35 ) )
      | ( ( k9_mcart_1 @ X30 @ X31 @ X32 @ X35 @ ( k4_mcart_1 @ X37 @ X36 @ X38 @ X39 ) )
        = X36 )
      | ~ ( m1_subset_1 @ ( k9_mcart_1 @ X30 @ X31 @ X32 @ X35 @ ( k4_mcart_1 @ X37 @ X36 @ X38 @ X39 ) ) @ X31 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ) @ X2 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) )
        = sk_G_4 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E ) @ X2 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_G_4 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_G_4 )
    | ~ ( m1_subset_1 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ) )).

thf('10',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( m1_subset_1 @ ( k9_mcart_1 @ X55 @ X56 @ X57 @ X58 @ X59 ) @ X56 )
      | ~ ( m1_subset_1 @ X59 @ ( k4_zfmisc_1 @ X55 @ X56 @ X57 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_mcart_1])).

thf('11',plain,(
    m1_subset_1 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_G_4 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G_4 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H_4 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G_4 )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G_4 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ D )
                 => ( ( F
                      = ( k11_mcart_1 @ A @ B @ C @ D @ E ) )
                  <=> ! [G: $i,H: $i,I: $i,J: $i] :
                        ( ( E
                          = ( k4_mcart_1 @ G @ H @ I @ J ) )
                       => ( F = J ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X13 @ X14 )
      | ( X13
       != ( k11_mcart_1 @ X10 @ X11 @ X12 @ X14 @ X15 ) )
      | ( X13 = X16 )
      | ( X15
       != ( k4_mcart_1 @ X17 @ X18 @ X19 @ X16 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d11_mcart_1])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X17 @ X18 @ X19 @ X16 ) @ ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14 ) )
      | ( ( k11_mcart_1 @ X10 @ X11 @ X12 @ X14 @ ( k4_mcart_1 @ X17 @ X18 @ X19 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ ( k11_mcart_1 @ X10 @ X11 @ X12 @ X14 @ ( k4_mcart_1 @ X17 @ X18 @ X19 @ X16 ) ) @ X14 )
      | ( X12 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ) @ X0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) )
        = sk_I_4 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E ) @ X0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_I_4 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_I_4 )
    | ~ ( m1_subset_1 @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ) )).

thf('28',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( m1_subset_1 @ ( k11_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_mcart_1])).

thf('29',plain,(
    m1_subset_1 @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_I_4 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_I_4 ),
    inference('simplify_reflect-',[status(thm)],['30','31','32','33','34'])).

thf('36',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I_4 )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I_4 ) ),
    inference(split,[status(esa)],['16'])).

thf('37',plain,
    ( ( sk_I_4 != sk_I_4 )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I_4 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_I_4 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ C )
                 => ( ( F
                      = ( k10_mcart_1 @ A @ B @ C @ D @ E ) )
                  <=> ! [G: $i,H: $i,I: $i,J: $i] :
                        ( ( E
                          = ( k4_mcart_1 @ G @ H @ I @ J ) )
                       => ( F = I ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ X2 )
      | ( X3
       != ( k10_mcart_1 @ X0 @ X1 @ X2 @ X5 @ X4 ) )
      | ( X3 = X6 )
      | ( X4
       != ( k4_mcart_1 @ X7 @ X8 @ X6 @ X9 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X5 ) )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d10_mcart_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X7 @ X8 @ X6 @ X9 ) @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X5 ) )
      | ( ( k10_mcart_1 @ X0 @ X1 @ X2 @ X5 @ ( k4_mcart_1 @ X7 @ X8 @ X6 @ X9 ) )
        = X6 )
      | ~ ( m1_subset_1 @ ( k10_mcart_1 @ X0 @ X1 @ X2 @ X5 @ ( k4_mcart_1 @ X7 @ X8 @ X6 @ X9 ) ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ) @ X1 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) )
        = sk_H_4 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E ) @ X1 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_H_4 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_H_4 )
    | ~ ( m1_subset_1 @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ) )).

thf('49',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( m1_subset_1 @ ( k10_mcart_1 @ X40 @ X41 @ X42 @ X43 @ X44 ) @ X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_mcart_1])).

thf('50',plain,(
    m1_subset_1 @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_H_4 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H_4 ),
    inference('simplify_reflect-',[status(thm)],['51','52','53','54','55'])).

thf('57',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H_4 )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H_4 ) ),
    inference(split,[status(esa)],['16'])).

thf('58',plain,
    ( ( sk_H_4 != sk_H_4 )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H_4 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H_4 ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ( ( F
                      = ( k8_mcart_1 @ A @ B @ C @ D @ E ) )
                  <=> ! [G: $i,H: $i,I: $i,J: $i] :
                        ( ( E
                          = ( k4_mcart_1 @ G @ H @ I @ J ) )
                       => ( F = G ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X23 @ X20 )
      | ( X23
       != ( k8_mcart_1 @ X20 @ X21 @ X22 @ X25 @ X24 ) )
      | ( X23 = X26 )
      | ( X24
       != ( k4_mcart_1 @ X26 @ X27 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d8_mcart_1])).

thf('63',plain,(
    ! [X20: $i,X21: $i,X22: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X26 @ X27 @ X28 @ X29 ) @ ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X25 ) )
      | ( ( k8_mcart_1 @ X20 @ X21 @ X22 @ X25 @ ( k4_mcart_1 @ X26 @ X27 @ X28 @ X29 ) )
        = X26 )
      | ~ ( m1_subset_1 @ ( k8_mcart_1 @ X20 @ X21 @ X22 @ X25 @ ( k4_mcart_1 @ X26 @ X27 @ X28 @ X29 ) ) @ X20 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ) @ X3 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) )
        = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G_4 @ sk_H_4 @ sk_I_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E ) @ X3 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_F )
    | ~ ( m1_subset_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ) )).

thf('70',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( m1_subset_1 @ ( k8_mcart_1 @ X50 @ X51 @ X52 @ X53 @ X54 ) @ X50 )
      | ~ ( m1_subset_1 @ X54 @ ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_mcart_1])).

thf('71',plain,(
    m1_subset_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_F )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_F ),
    inference('simplify_reflect-',[status(thm)],['72','73','74','75','76'])).

thf('78',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference(split,[status(esa)],['16'])).

thf('79',plain,
    ( ( sk_F != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_F ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G_4 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H_4 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I_4 ) ),
    inference(split,[status(esa)],['16'])).

thf('82',plain,(
    ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_G_4 ),
    inference('sat_resolution*',[status(thm)],['38','59','80','81'])).

thf('83',plain,(
    ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_G_4 ),
    inference(simpl_trail,[status(thm)],['17','82'])).

thf('84',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15','83','84'])).


%------------------------------------------------------------------------------
