%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yi6oBOuiWB

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:11 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 632 expanded)
%              Number of leaves         :   24 ( 203 expanded)
%              Depth                    :   15
%              Number of atoms          : 1523 (19568 expanded)
%              Number of equality atoms :  185 (2752 expanded)
%              Maximal formula depth    :   26 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(sk_J_type,type,(
    sk_J: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_1_type,type,(
    sk_G_1: $i > $i > $i > $i > $i > $i )).

thf(sk_H_1_type,type,(
    sk_H_1: $i > $i > $i > $i > $i > $i )).

thf(sk_I_1_type,type,(
    sk_I_1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i )).

thf(t79_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( ! [G: $i] :
            ( ( m1_subset_1 @ G @ A )
           => ! [H: $i] :
                ( ( m1_subset_1 @ H @ B )
               => ! [I: $i] :
                    ( ( m1_subset_1 @ I @ C )
                   => ! [J: $i] :
                        ( ( m1_subset_1 @ J @ D )
                       => ( ( F
                            = ( k4_mcart_1 @ G @ H @ I @ J ) )
                         => ( E = G ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k8_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
       => ( ! [G: $i] :
              ( ( m1_subset_1 @ G @ A )
             => ! [H: $i] :
                  ( ( m1_subset_1 @ H @ B )
                 => ! [I: $i] :
                      ( ( m1_subset_1 @ I @ C )
                     => ! [J: $i] :
                          ( ( m1_subset_1 @ J @ D )
                         => ( ( F
                              = ( k4_mcart_1 @ G @ H @ I @ J ) )
                           => ( E = G ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k8_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13
        = ( k4_mcart_1 @ ( sk_F @ X13 @ X14 @ X12 @ X11 @ X10 ) @ ( sk_G_1 @ X13 @ X14 @ X12 @ X11 @ X10 ) @ ( sk_H_1 @ X13 @ X14 @ X12 @ X11 @ X10 ) @ ( sk_I_1 @ X13 @ X14 @ X12 @ X11 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F_1
      = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G_1 @ X13 @ X14 @ X12 @ X11 @ X10 ) @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('10',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['10','11','12','13','14'])).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ sk_B )
      | ~ ( m1_subset_1 @ X24 @ sk_D )
      | ( sk_F_1
       != ( k4_mcart_1 @ X25 @ X23 @ X26 @ X24 ) )
      | ( sk_E = X25 )
      | ~ ( m1_subset_1 @ X26 @ sk_C )
      | ~ ( m1_subset_1 @ X25 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E = X0 )
      | ( sk_F_1
       != ( k4_mcart_1 @ X0 @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ~ ( m1_subset_1 @ ( sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_E
      = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_I_1 @ X13 @ X14 @ X12 @ X11 @ X10 ) @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('21',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_H_1 @ X13 @ X14 @ X12 @ X11 @ X10 ) @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('29',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X13 @ X14 @ X12 @ X11 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('37',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['37','38','39','40','41'])).

thf('43',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ( sk_E
      = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','26','34','42'])).

thf('44',plain,
    ( sk_E
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('46',plain,(
    m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['37','38','39','40','41'])).

thf('47',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
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

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ X0 )
      | ( X4
        = ( k4_mcart_1 @ ( sk_G @ X3 @ X4 ) @ ( sk_H @ X3 @ X4 ) @ ( sk_I @ X3 @ X4 ) @ ( sk_J @ X3 @ X4 ) ) )
      | ( X3
        = ( k8_mcart_1 @ X0 @ X1 @ X2 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X5 ) )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d8_mcart_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( X0
        = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
      | ( sk_F_1
        = ( k4_mcart_1 @ ( sk_G @ X0 @ sk_F_1 ) @ ( sk_H @ X0 @ sk_F_1 ) @ ( sk_I @ X0 @ sk_F_1 ) @ ( sk_J @ X0 @ sk_F_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
      | ( sk_F_1
        = ( k4_mcart_1 @ ( sk_G @ X0 @ sk_F_1 ) @ ( sk_H @ X0 @ sk_F_1 ) @ ( sk_I @ X0 @ sk_F_1 ) @ ( sk_J @ X0 @ sk_F_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( sk_F_1
      = ( k4_mcart_1 @ ( sk_G @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_H @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_I @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_J @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf(t33_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_mcart_1 @ A @ B @ C @ D )
        = ( k4_mcart_1 @ E @ F @ G @ H ) )
     => ( ( A = E )
        & ( B = F )
        & ( C = G )
        & ( D = H ) ) ) )).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X16 = X15 )
      | ( ( k4_mcart_1 @ X16 @ X20 @ X21 @ X22 )
       != ( k4_mcart_1 @ X15 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t33_mcart_1])).

thf('57',plain,(
    ! [X16: $i,X20: $i,X21: $i,X22: $i] :
      ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ X16 @ X20 @ X21 @ X22 ) )
      = X16 ) ),
    inference(inj_rec,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( '#_fresh_sk1' @ sk_F_1 )
      = ( sk_G @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup+',[status(thm)],['55','57'])).

thf('59',plain,
    ( ( sk_F_1
      = ( k4_mcart_1 @ ( sk_G @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_H @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_I @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_J @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('60',plain,
    ( ( sk_F_1
      = ( k4_mcart_1 @ ( '#_fresh_sk1' @ sk_F_1 ) @ ( sk_H @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_I @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_J @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( sk_F_1
      = ( k4_mcart_1 @ ( '#_fresh_sk1' @ sk_F_1 ) @ ( sk_H @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_I @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_J @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X16 = X15 )
      | ( ( k4_mcart_1 @ X16 @ X20 @ X21 @ X22 )
       != ( k4_mcart_1 @ X15 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t33_mcart_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
       != sk_F_1 )
      | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
        = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
      | ( X3
        = ( '#_fresh_sk1' @ sk_F_1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( '#_fresh_sk1' @ sk_F_1 ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup-',[status(thm)],['45','63'])).

thf('65',plain,
    ( ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( '#_fresh_sk1' @ sk_F_1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( sk_E
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('67',plain,
    ( ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( sk_E
      = ( '#_fresh_sk1' @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( '#_fresh_sk1' @ sk_F_1 )
      = ( sk_G @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup+',[status(thm)],['55','57'])).

thf('69',plain,(
    m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['37','38','39','40','41'])).

thf('70',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ X0 )
      | ( X3
       != ( sk_G @ X3 @ X4 ) )
      | ( X3
        = ( k8_mcart_1 @ X0 @ X1 @ X2 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X5 ) )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d8_mcart_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( X0
        = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
      | ( X0
       != ( sk_G @ X0 @ sk_F_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

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

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
      | ( X0
       != ( sk_G @ X0 @ sk_F_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['72','73','74','75','76'])).

thf('78',plain,
    ( ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
     != ( sk_G @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,
    ( ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
     != ( '#_fresh_sk1' @ sk_F_1 ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup-',[status(thm)],['68','78'])).

thf('80',plain,
    ( ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
     != ( '#_fresh_sk1' @ sk_F_1 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( sk_E
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('82',plain,
    ( sk_E
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('83',plain,
    ( ( sk_E
      = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( sk_E
     != ( '#_fresh_sk1' @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    sk_E
 != ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_E
 != ( '#_fresh_sk1' @ sk_F_1 ) ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
    = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference('simplify_reflect-',[status(thm)],['67','85'])).

thf('87',plain,
    ( sk_E
    = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference('sup+',[status(thm)],['44','86'])).

thf('88',plain,(
    sk_E
 != ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yi6oBOuiWB
% 0.16/0.37  % Computer   : n024.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:29:21 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 194 iterations in 0.103s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.40/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.60  thf(sk_I_type, type, sk_I: $i > $i > $i).
% 0.40/0.60  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.40/0.60  thf(sk_J_type, type, sk_J: $i > $i > $i).
% 0.40/0.60  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.40/0.60  thf(sk_G_type, type, sk_G: $i > $i > $i).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 0.40/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.40/0.60  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(sk_G_1_type, type, sk_G_1: $i > $i > $i > $i > $i > $i).
% 0.40/0.60  thf(sk_H_1_type, type, sk_H_1: $i > $i > $i > $i > $i > $i).
% 0.40/0.60  thf(sk_I_1_type, type, sk_I_1: $i > $i > $i > $i > $i > $i).
% 0.40/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.60  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.40/0.60  thf(sk_H_type, type, sk_H: $i > $i > $i).
% 0.40/0.60  thf(t79_mcart_1, conjecture,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.40/0.60       ( ( ![G:$i]:
% 0.40/0.60           ( ( m1_subset_1 @ G @ A ) =>
% 0.40/0.60             ( ![H:$i]:
% 0.40/0.60               ( ( m1_subset_1 @ H @ B ) =>
% 0.40/0.60                 ( ![I:$i]:
% 0.40/0.60                   ( ( m1_subset_1 @ I @ C ) =>
% 0.40/0.60                     ( ![J:$i]:
% 0.40/0.60                       ( ( m1_subset_1 @ J @ D ) =>
% 0.40/0.60                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.40/0.60                           ( ( E ) = ( G ) ) ) ) ) ) ) ) ) ) ) =>
% 0.40/0.60         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.40/0.60           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.40/0.60           ( ( E ) = ( k8_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.60        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.40/0.60          ( ( ![G:$i]:
% 0.40/0.60              ( ( m1_subset_1 @ G @ A ) =>
% 0.40/0.60                ( ![H:$i]:
% 0.40/0.60                  ( ( m1_subset_1 @ H @ B ) =>
% 0.40/0.60                    ( ![I:$i]:
% 0.40/0.60                      ( ( m1_subset_1 @ I @ C ) =>
% 0.40/0.60                        ( ![J:$i]:
% 0.40/0.60                          ( ( m1_subset_1 @ J @ D ) =>
% 0.40/0.60                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.40/0.60                              ( ( E ) = ( G ) ) ) ) ) ) ) ) ) ) ) =>
% 0.40/0.60            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.40/0.60              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.40/0.60              ( ( E ) = ( k8_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t79_mcart_1])).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(l68_mcart_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.60          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.40/0.60          ( ?[E:$i]:
% 0.40/0.60            ( ( ![F:$i]:
% 0.40/0.60                ( ( m1_subset_1 @ F @ A ) =>
% 0.40/0.60                  ( ![G:$i]:
% 0.40/0.60                    ( ( m1_subset_1 @ G @ B ) =>
% 0.40/0.60                      ( ![H:$i]:
% 0.40/0.60                        ( ( m1_subset_1 @ H @ C ) =>
% 0.40/0.60                          ( ![I:$i]:
% 0.40/0.60                            ( ( m1_subset_1 @ I @ D ) =>
% 0.40/0.60                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.40/0.60              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.60         (((X10) = (k1_xboole_0))
% 0.40/0.60          | ((X11) = (k1_xboole_0))
% 0.40/0.60          | ((X12) = (k1_xboole_0))
% 0.40/0.60          | ((X13)
% 0.40/0.60              = (k4_mcart_1 @ (sk_F @ X13 @ X14 @ X12 @ X11 @ X10) @ 
% 0.40/0.60                 (sk_G_1 @ X13 @ X14 @ X12 @ X11 @ X10) @ 
% 0.40/0.60                 (sk_H_1 @ X13 @ X14 @ X12 @ X11 @ X10) @ 
% 0.40/0.60                 (sk_I_1 @ X13 @ X14 @ X12 @ X11 @ X10)))
% 0.40/0.60          | ~ (m1_subset_1 @ X13 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14))
% 0.40/0.60          | ((X14) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      ((((sk_D) = (k1_xboole_0))
% 0.40/0.60        | ((sk_F_1)
% 0.40/0.60            = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.40/0.60               (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.40/0.60               (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.40/0.60               (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.40/0.60        | ((sk_C) = (k1_xboole_0))
% 0.40/0.60        | ((sk_B) = (k1_xboole_0))
% 0.40/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.60  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (((sk_F_1)
% 0.40/0.60         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.40/0.60            (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.40/0.60            (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.40/0.60            (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.60         (((X10) = (k1_xboole_0))
% 0.40/0.60          | ((X11) = (k1_xboole_0))
% 0.40/0.60          | ((X12) = (k1_xboole_0))
% 0.40/0.60          | (m1_subset_1 @ (sk_G_1 @ X13 @ X14 @ X12 @ X11 @ X10) @ X11)
% 0.40/0.60          | ~ (m1_subset_1 @ X13 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14))
% 0.40/0.60          | ((X14) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      ((((sk_D) = (k1_xboole_0))
% 0.40/0.60        | (m1_subset_1 @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.40/0.60        | ((sk_C) = (k1_xboole_0))
% 0.40/0.60        | ((sk_B) = (k1_xboole_0))
% 0.40/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.60  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('13', plain, (((sk_C) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('14', plain, (((sk_D) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      ((m1_subset_1 @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)],
% 0.40/0.60                ['10', '11', '12', '13', '14'])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X23 @ sk_B)
% 0.40/0.60          | ~ (m1_subset_1 @ X24 @ sk_D)
% 0.40/0.60          | ((sk_F_1) != (k4_mcart_1 @ X25 @ X23 @ X26 @ X24))
% 0.40/0.60          | ((sk_E) = (X25))
% 0.40/0.60          | ~ (m1_subset_1 @ X26 @ sk_C)
% 0.40/0.60          | ~ (m1_subset_1 @ X25 @ sk_A))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.40/0.60          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.40/0.60          | ((sk_E) = (X0))
% 0.40/0.60          | ((sk_F_1)
% 0.40/0.60              != (k4_mcart_1 @ X0 @ 
% 0.40/0.60                  (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ X1 @ X2))
% 0.40/0.60          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.40/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      ((((sk_F_1) != (sk_F_1))
% 0.40/0.60        | ~ (m1_subset_1 @ (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.40/0.60        | ((sk_E) = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.40/0.60        | ~ (m1_subset_1 @ (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.40/0.60        | ~ (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['7', '17'])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.60         (((X10) = (k1_xboole_0))
% 0.40/0.60          | ((X11) = (k1_xboole_0))
% 0.40/0.60          | ((X12) = (k1_xboole_0))
% 0.40/0.60          | (m1_subset_1 @ (sk_I_1 @ X13 @ X14 @ X12 @ X11 @ X10) @ X14)
% 0.40/0.60          | ~ (m1_subset_1 @ X13 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14))
% 0.40/0.60          | ((X14) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      ((((sk_D) = (k1_xboole_0))
% 0.40/0.60        | (m1_subset_1 @ (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.40/0.60        | ((sk_C) = (k1_xboole_0))
% 0.40/0.60        | ((sk_B) = (k1_xboole_0))
% 0.40/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.60  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('25', plain, (((sk_D) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      ((m1_subset_1 @ (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)],
% 0.40/0.60                ['21', '22', '23', '24', '25'])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.60         (((X10) = (k1_xboole_0))
% 0.40/0.60          | ((X11) = (k1_xboole_0))
% 0.40/0.60          | ((X12) = (k1_xboole_0))
% 0.40/0.60          | (m1_subset_1 @ (sk_H_1 @ X13 @ X14 @ X12 @ X11 @ X10) @ X12)
% 0.40/0.60          | ~ (m1_subset_1 @ X13 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14))
% 0.40/0.60          | ((X14) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      ((((sk_D) = (k1_xboole_0))
% 0.40/0.60        | (m1_subset_1 @ (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.40/0.60        | ((sk_C) = (k1_xboole_0))
% 0.40/0.60        | ((sk_B) = (k1_xboole_0))
% 0.40/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.40/0.60  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('31', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('32', plain, (((sk_C) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('33', plain, (((sk_D) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      ((m1_subset_1 @ (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)],
% 0.40/0.60                ['29', '30', '31', '32', '33'])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.60         (((X10) = (k1_xboole_0))
% 0.40/0.60          | ((X11) = (k1_xboole_0))
% 0.40/0.60          | ((X12) = (k1_xboole_0))
% 0.40/0.60          | (m1_subset_1 @ (sk_F @ X13 @ X14 @ X12 @ X11 @ X10) @ X10)
% 0.40/0.60          | ~ (m1_subset_1 @ X13 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14))
% 0.40/0.60          | ((X14) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.40/0.60  thf('37', plain,
% 0.40/0.60      ((((sk_D) = (k1_xboole_0))
% 0.40/0.60        | (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.40/0.60        | ((sk_C) = (k1_xboole_0))
% 0.40/0.60        | ((sk_B) = (k1_xboole_0))
% 0.40/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.60  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('39', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('40', plain, (((sk_C) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('41', plain, (((sk_D) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('42', plain,
% 0.40/0.60      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)],
% 0.40/0.60                ['37', '38', '39', '40', '41'])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      ((((sk_F_1) != (sk_F_1))
% 0.40/0.60        | ((sk_E) = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.40/0.60      inference('demod', [status(thm)], ['18', '26', '34', '42'])).
% 0.40/0.60  thf('44', plain, (((sk_E) = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.40/0.60  thf('45', plain,
% 0.40/0.60      (((sk_F_1)
% 0.40/0.60         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.40/0.60            (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.40/0.60            (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.40/0.60            (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.40/0.60  thf('46', plain,
% 0.40/0.60      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)],
% 0.40/0.60                ['37', '38', '39', '40', '41'])).
% 0.40/0.60  thf('47', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(d8_mcart_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.60          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.40/0.60          ( ~( ![E:$i]:
% 0.40/0.60               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.40/0.60                 ( ![F:$i]:
% 0.40/0.60                   ( ( m1_subset_1 @ F @ A ) =>
% 0.40/0.60                     ( ( ( F ) = ( k8_mcart_1 @ A @ B @ C @ D @ E ) ) <=>
% 0.40/0.60                       ( ![G:$i,H:$i,I:$i,J:$i]:
% 0.40/0.60                         ( ( ( E ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.40/0.60                           ( ( F ) = ( G ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.60  thf('48', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.60         (((X0) = (k1_xboole_0))
% 0.40/0.60          | ((X1) = (k1_xboole_0))
% 0.40/0.60          | ((X2) = (k1_xboole_0))
% 0.40/0.60          | ~ (m1_subset_1 @ X3 @ X0)
% 0.40/0.60          | ((X4)
% 0.40/0.60              = (k4_mcart_1 @ (sk_G @ X3 @ X4) @ (sk_H @ X3 @ X4) @ 
% 0.40/0.60                 (sk_I @ X3 @ X4) @ (sk_J @ X3 @ X4)))
% 0.40/0.60          | ((X3) = (k8_mcart_1 @ X0 @ X1 @ X2 @ X5 @ X4))
% 0.40/0.60          | ~ (m1_subset_1 @ X4 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X5))
% 0.40/0.60          | ((X5) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d8_mcart_1])).
% 0.40/0.60  thf('49', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((sk_D) = (k1_xboole_0))
% 0.40/0.60          | ((X0) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60          | ((sk_F_1)
% 0.40/0.60              = (k4_mcart_1 @ (sk_G @ X0 @ sk_F_1) @ (sk_H @ X0 @ sk_F_1) @ 
% 0.40/0.60                 (sk_I @ X0 @ sk_F_1) @ (sk_J @ X0 @ sk_F_1)))
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.40/0.60          | ((sk_C) = (k1_xboole_0))
% 0.40/0.60          | ((sk_B) = (k1_xboole_0))
% 0.40/0.60          | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.60  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('51', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('52', plain, (((sk_C) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('53', plain, (((sk_D) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('54', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((X0) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60          | ((sk_F_1)
% 0.40/0.60              = (k4_mcart_1 @ (sk_G @ X0 @ sk_F_1) @ (sk_H @ X0 @ sk_F_1) @ 
% 0.40/0.60                 (sk_I @ X0 @ sk_F_1) @ (sk_J @ X0 @ sk_F_1)))
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)],
% 0.40/0.60                ['49', '50', '51', '52', '53'])).
% 0.40/0.60  thf('55', plain,
% 0.40/0.60      ((((sk_F_1)
% 0.40/0.60          = (k4_mcart_1 @ 
% 0.40/0.60             (sk_G @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.40/0.60             (sk_H @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.40/0.60             (sk_I @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.40/0.60             (sk_J @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1)))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['46', '54'])).
% 0.40/0.60  thf(t33_mcart_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.40/0.60     ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.40/0.60       ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.40/0.60         ( ( D ) = ( H ) ) ) ))).
% 0.40/0.60  thf('56', plain,
% 0.40/0.60      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, 
% 0.40/0.60         X22 : $i]:
% 0.40/0.60         (((X16) = (X15))
% 0.40/0.60          | ((k4_mcart_1 @ X16 @ X20 @ X21 @ X22)
% 0.40/0.60              != (k4_mcart_1 @ X15 @ X17 @ X18 @ X19)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t33_mcart_1])).
% 0.40/0.60  thf('57', plain,
% 0.40/0.60      (![X16 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.60         (('#_fresh_sk1' @ (k4_mcart_1 @ X16 @ X20 @ X21 @ X22)) = (X16))),
% 0.40/0.60      inference('inj_rec', [status(thm)], ['56'])).
% 0.40/0.60  thf('58', plain,
% 0.40/0.60      (((('#_fresh_sk1' @ sk_F_1)
% 0.40/0.60          = (sk_G @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['55', '57'])).
% 0.40/0.60  thf('59', plain,
% 0.40/0.60      ((((sk_F_1)
% 0.40/0.60          = (k4_mcart_1 @ 
% 0.40/0.60             (sk_G @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.40/0.60             (sk_H @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.40/0.60             (sk_I @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.40/0.60             (sk_J @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1)))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['46', '54'])).
% 0.40/0.60  thf('60', plain,
% 0.40/0.60      ((((sk_F_1)
% 0.40/0.60          = (k4_mcart_1 @ ('#_fresh_sk1' @ sk_F_1) @ 
% 0.40/0.60             (sk_H @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.40/0.60             (sk_I @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.40/0.60             (sk_J @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1)))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['58', '59'])).
% 0.40/0.60  thf('61', plain,
% 0.40/0.60      ((((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60          = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60        | ((sk_F_1)
% 0.40/0.60            = (k4_mcart_1 @ ('#_fresh_sk1' @ sk_F_1) @ 
% 0.40/0.60               (sk_H @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.40/0.60               (sk_I @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.40/0.60               (sk_J @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1))))),
% 0.40/0.60      inference('simplify', [status(thm)], ['60'])).
% 0.40/0.60  thf('62', plain,
% 0.40/0.60      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, 
% 0.40/0.60         X22 : $i]:
% 0.40/0.60         (((X16) = (X15))
% 0.40/0.60          | ((k4_mcart_1 @ X16 @ X20 @ X21 @ X22)
% 0.40/0.60              != (k4_mcart_1 @ X15 @ X17 @ X18 @ X19)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t33_mcart_1])).
% 0.40/0.60  thf('63', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.60         (((k4_mcart_1 @ X3 @ X2 @ X1 @ X0) != (sk_F_1))
% 0.40/0.60          | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60              = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60          | ((X3) = ('#_fresh_sk1' @ sk_F_1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['61', '62'])).
% 0.40/0.60  thf('64', plain,
% 0.40/0.60      ((((sk_F_1) != (sk_F_1))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = ('#_fresh_sk1' @ sk_F_1))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['45', '63'])).
% 0.40/0.60  thf('65', plain,
% 0.40/0.60      ((((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60          = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = ('#_fresh_sk1' @ sk_F_1)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['64'])).
% 0.40/0.60  thf('66', plain, (((sk_E) = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.40/0.60  thf('67', plain,
% 0.40/0.60      ((((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60          = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60        | ((sk_E) = ('#_fresh_sk1' @ sk_F_1)))),
% 0.40/0.60      inference('demod', [status(thm)], ['65', '66'])).
% 0.40/0.60  thf('68', plain,
% 0.40/0.60      (((('#_fresh_sk1' @ sk_F_1)
% 0.40/0.60          = (sk_G @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['55', '57'])).
% 0.40/0.60  thf('69', plain,
% 0.40/0.60      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)],
% 0.40/0.60                ['37', '38', '39', '40', '41'])).
% 0.40/0.60  thf('70', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('71', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.60         (((X0) = (k1_xboole_0))
% 0.40/0.60          | ((X1) = (k1_xboole_0))
% 0.40/0.60          | ((X2) = (k1_xboole_0))
% 0.40/0.60          | ~ (m1_subset_1 @ X3 @ X0)
% 0.40/0.60          | ((X3) != (sk_G @ X3 @ X4))
% 0.40/0.60          | ((X3) = (k8_mcart_1 @ X0 @ X1 @ X2 @ X5 @ X4))
% 0.40/0.60          | ~ (m1_subset_1 @ X4 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X5))
% 0.40/0.60          | ((X5) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d8_mcart_1])).
% 0.40/0.60  thf('72', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((sk_D) = (k1_xboole_0))
% 0.40/0.60          | ((X0) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60          | ((X0) != (sk_G @ X0 @ sk_F_1))
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.40/0.60          | ((sk_C) = (k1_xboole_0))
% 0.40/0.60          | ((sk_B) = (k1_xboole_0))
% 0.40/0.60          | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.40/0.60  thf('73', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('74', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('75', plain, (((sk_C) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('76', plain, (((sk_D) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('77', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((X0) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60          | ((X0) != (sk_G @ X0 @ sk_F_1))
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)],
% 0.40/0.60                ['72', '73', '74', '75', '76'])).
% 0.40/0.60  thf('78', plain,
% 0.40/0.60      ((((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60          != (sk_G @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['69', '77'])).
% 0.40/0.60  thf('79', plain,
% 0.40/0.60      ((((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60          != ('#_fresh_sk1' @ sk_F_1))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['68', '78'])).
% 0.40/0.60  thf('80', plain,
% 0.40/0.60      ((((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60          = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60        | ((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60            != ('#_fresh_sk1' @ sk_F_1)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['79'])).
% 0.40/0.60  thf('81', plain, (((sk_E) = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.40/0.60  thf('82', plain, (((sk_E) = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.40/0.60  thf('83', plain,
% 0.40/0.60      ((((sk_E) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.40/0.60        | ((sk_E) != ('#_fresh_sk1' @ sk_F_1)))),
% 0.40/0.60      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.40/0.60  thf('84', plain,
% 0.40/0.60      (((sk_E) != (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('85', plain, (((sk_E) != ('#_fresh_sk1' @ sk_F_1))),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 0.40/0.60  thf('86', plain,
% 0.40/0.60      (((sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.40/0.60         = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)], ['67', '85'])).
% 0.40/0.60  thf('87', plain,
% 0.40/0.60      (((sk_E) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['44', '86'])).
% 0.40/0.60  thf('88', plain,
% 0.40/0.60      (((sk_E) != (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('89', plain, ($false),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
