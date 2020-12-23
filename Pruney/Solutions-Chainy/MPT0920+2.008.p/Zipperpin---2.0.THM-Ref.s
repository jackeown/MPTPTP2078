%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6RYMOLtayP

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:12 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 678 expanded)
%              Number of leaves         :   25 ( 217 expanded)
%              Depth                    :   17
%              Number of atoms          : 1707 (21050 expanded)
%              Number of equality atoms :  197 (2951 expanded)
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

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

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

thf(t80_mcart_1,conjecture,(
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
                         => ( E = H ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

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
                           => ( E = H ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_mcart_1])).

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
      | ( sk_E = X23 )
      | ~ ( m1_subset_1 @ X26 @ sk_C )
      | ~ ( m1_subset_1 @ X25 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
        = ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( sk_F_1
       != ( k4_mcart_1 @ X0 @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ~ ( m1_subset_1 @ ( sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_E
      = ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
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
      = ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','26','34','42'])).

thf('44',plain,
    ( sk_E
    = ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('46',plain,(
    m1_subset_1 @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['10','11','12','13','14'])).

thf('47',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
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

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ X1 )
      | ( X4
        = ( k4_mcart_1 @ ( sk_G @ X3 @ X4 ) @ ( sk_H @ X3 @ X4 ) @ ( sk_I @ X3 @ X4 ) @ ( sk_J @ X3 @ X4 ) ) )
      | ( X3
        = ( k9_mcart_1 @ X0 @ X1 @ X2 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X5 ) )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d9_mcart_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
      | ( sk_F_1
        = ( k4_mcart_1 @ ( sk_G @ X0 @ sk_F_1 ) @ ( sk_H @ X0 @ sk_F_1 ) @ ( sk_I @ X0 @ sk_F_1 ) @ ( sk_J @ X0 @ sk_F_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
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
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
      | ( sk_F_1
        = ( k4_mcart_1 @ ( sk_G @ X0 @ sk_F_1 ) @ ( sk_H @ X0 @ sk_F_1 ) @ ( sk_I @ X0 @ sk_F_1 ) @ ( sk_J @ X0 @ sk_F_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( sk_F_1
      = ( k4_mcart_1 @ ( sk_G @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_H @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_I @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_J @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
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
      ( ( X20 = X17 )
      | ( ( k4_mcart_1 @ X16 @ X20 @ X21 @ X22 )
       != ( k4_mcart_1 @ X15 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t33_mcart_1])).

thf('57',plain,(
    ! [X16: $i,X20: $i,X21: $i,X22: $i] :
      ( ( '#_fresh_sk2' @ ( k4_mcart_1 @ X16 @ X20 @ X21 @ X22 ) )
      = X20 ) ),
    inference(inj_rec,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( '#_fresh_sk2' @ sk_F_1 )
      = ( sk_H @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup+',[status(thm)],['55','57'])).

thf('59',plain,
    ( ( sk_F_1
      = ( k4_mcart_1 @ ( sk_G @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_H @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_I @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_J @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X16 = X15 )
      | ( ( k4_mcart_1 @ X16 @ X20 @ X21 @ X22 )
       != ( k4_mcart_1 @ X15 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t33_mcart_1])).

thf('61',plain,(
    ! [X16: $i,X20: $i,X21: $i,X22: $i] :
      ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ X16 @ X20 @ X21 @ X22 ) )
      = X16 ) ),
    inference(inj_rec,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( '#_fresh_sk1' @ sk_F_1 )
      = ( sk_G @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup+',[status(thm)],['59','61'])).

thf('63',plain,
    ( ( sk_F_1
      = ( k4_mcart_1 @ ( sk_G @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_H @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_I @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_J @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('64',plain,
    ( ( sk_F_1
      = ( k4_mcart_1 @ ( '#_fresh_sk1' @ sk_F_1 ) @ ( sk_H @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_I @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_J @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( sk_F_1
      = ( k4_mcart_1 @ ( '#_fresh_sk1' @ sk_F_1 ) @ ( sk_H @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_I @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_J @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_F_1
      = ( k4_mcart_1 @ ( '#_fresh_sk1' @ sk_F_1 ) @ ( '#_fresh_sk2' @ sk_F_1 ) @ ( sk_I @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_J @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup+',[status(thm)],['58','65'])).

thf('67',plain,
    ( ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( sk_F_1
      = ( k4_mcart_1 @ ( '#_fresh_sk1' @ sk_F_1 ) @ ( '#_fresh_sk2' @ sk_F_1 ) @ ( sk_I @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) @ ( sk_J @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 = X17 )
      | ( ( k4_mcart_1 @ X16 @ X20 @ X21 @ X22 )
       != ( k4_mcart_1 @ X15 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t33_mcart_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
       != sk_F_1 )
      | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
      | ( X2
        = ( '#_fresh_sk2' @ sk_F_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( '#_fresh_sk2' @ sk_F_1 ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup-',[status(thm)],['45','69'])).

thf('71',plain,
    ( ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( '#_fresh_sk2' @ sk_F_1 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( sk_E
    = ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('73',plain,
    ( ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( sk_E
      = ( '#_fresh_sk2' @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( '#_fresh_sk2' @ sk_F_1 )
      = ( sk_H @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup+',[status(thm)],['55','57'])).

thf('75',plain,(
    m1_subset_1 @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['10','11','12','13','14'])).

thf('76',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ X1 )
      | ( X3
       != ( sk_H @ X3 @ X4 ) )
      | ( X3
        = ( k9_mcart_1 @ X0 @ X1 @ X2 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X5 ) )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d9_mcart_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
      | ( X0
       != ( sk_H @ X0 @ sk_F_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
      | ( X0
       != ( sk_H @ X0 @ sk_F_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['78','79','80','81','82'])).

thf('84',plain,
    ( ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
     != ( sk_H @ ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_F_1 ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,
    ( ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
     != ( '#_fresh_sk2' @ sk_F_1 ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference('sup-',[status(thm)],['74','84'])).

thf('86',plain,
    ( ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
     != ( '#_fresh_sk2' @ sk_F_1 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( sk_E
    = ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('88',plain,
    ( sk_E
    = ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('89',plain,
    ( ( sk_E
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) )
    | ( sk_E
     != ( '#_fresh_sk2' @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    sk_E
 != ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    sk_E
 != ( '#_fresh_sk2' @ sk_F_1 ) ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
    = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference('simplify_reflect-',[status(thm)],['73','91'])).

thf('93',plain,
    ( sk_E
    = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference('sup+',[status(thm)],['44','92'])).

thf('94',plain,(
    sk_E
 != ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6RYMOLtayP
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 192 iterations in 0.101s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.56  thf(sk_I_type, type, sk_I: $i > $i > $i).
% 0.37/0.56  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.37/0.56  thf(sk_J_type, type, sk_J: $i > $i > $i).
% 0.37/0.56  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.37/0.56  thf(sk_G_type, type, sk_G: $i > $i > $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf('#_fresh_sk2_type', type, '#_fresh_sk2': $i > $i).
% 0.37/0.56  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 0.37/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.56  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(sk_G_1_type, type, sk_G_1: $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(sk_H_1_type, type, sk_H_1: $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(sk_I_1_type, type, sk_I_1: $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.37/0.56  thf(sk_H_type, type, sk_H: $i > $i > $i).
% 0.37/0.56  thf(t80_mcart_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.37/0.56       ( ( ![G:$i]:
% 0.37/0.56           ( ( m1_subset_1 @ G @ A ) =>
% 0.37/0.56             ( ![H:$i]:
% 0.37/0.56               ( ( m1_subset_1 @ H @ B ) =>
% 0.37/0.56                 ( ![I:$i]:
% 0.37/0.56                   ( ( m1_subset_1 @ I @ C ) =>
% 0.37/0.56                     ( ![J:$i]:
% 0.37/0.56                       ( ( m1_subset_1 @ J @ D ) =>
% 0.37/0.56                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.37/0.56                           ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.37/0.56         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.56           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.37/0.56           ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.56        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.37/0.56          ( ( ![G:$i]:
% 0.37/0.56              ( ( m1_subset_1 @ G @ A ) =>
% 0.37/0.56                ( ![H:$i]:
% 0.37/0.56                  ( ( m1_subset_1 @ H @ B ) =>
% 0.37/0.56                    ( ![I:$i]:
% 0.37/0.56                      ( ( m1_subset_1 @ I @ C ) =>
% 0.37/0.56                        ( ![J:$i]:
% 0.37/0.56                          ( ( m1_subset_1 @ J @ D ) =>
% 0.37/0.56                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.37/0.56                              ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.37/0.56            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.56              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.37/0.56              ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t80_mcart_1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(l68_mcart_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.56          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.37/0.56          ( ?[E:$i]:
% 0.37/0.56            ( ( ![F:$i]:
% 0.37/0.56                ( ( m1_subset_1 @ F @ A ) =>
% 0.37/0.56                  ( ![G:$i]:
% 0.37/0.56                    ( ( m1_subset_1 @ G @ B ) =>
% 0.37/0.56                      ( ![H:$i]:
% 0.37/0.56                        ( ( m1_subset_1 @ H @ C ) =>
% 0.37/0.56                          ( ![I:$i]:
% 0.37/0.56                            ( ( m1_subset_1 @ I @ D ) =>
% 0.37/0.56                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.37/0.56              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (((X10) = (k1_xboole_0))
% 0.37/0.56          | ((X11) = (k1_xboole_0))
% 0.37/0.56          | ((X12) = (k1_xboole_0))
% 0.37/0.56          | ((X13)
% 0.37/0.56              = (k4_mcart_1 @ (sk_F @ X13 @ X14 @ X12 @ X11 @ X10) @ 
% 0.37/0.56                 (sk_G_1 @ X13 @ X14 @ X12 @ X11 @ X10) @ 
% 0.37/0.56                 (sk_H_1 @ X13 @ X14 @ X12 @ X11 @ X10) @ 
% 0.37/0.56                 (sk_I_1 @ X13 @ X14 @ X12 @ X11 @ X10)))
% 0.37/0.56          | ~ (m1_subset_1 @ X13 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14))
% 0.37/0.56          | ((X14) = (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      ((((sk_D) = (k1_xboole_0))
% 0.37/0.56        | ((sk_F_1)
% 0.37/0.56            = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.37/0.56               (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.37/0.56               (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.37/0.56               (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.37/0.56        | ((sk_C) = (k1_xboole_0))
% 0.37/0.56        | ((sk_B) = (k1_xboole_0))
% 0.37/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.56  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (((sk_F_1)
% 0.37/0.56         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.37/0.56            (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.37/0.56            (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.37/0.56            (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (((X10) = (k1_xboole_0))
% 0.37/0.56          | ((X11) = (k1_xboole_0))
% 0.37/0.56          | ((X12) = (k1_xboole_0))
% 0.37/0.56          | (m1_subset_1 @ (sk_G_1 @ X13 @ X14 @ X12 @ X11 @ X10) @ X11)
% 0.37/0.56          | ~ (m1_subset_1 @ X13 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14))
% 0.37/0.56          | ((X14) = (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      ((((sk_D) = (k1_xboole_0))
% 0.37/0.56        | (m1_subset_1 @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.37/0.56        | ((sk_C) = (k1_xboole_0))
% 0.37/0.56        | ((sk_B) = (k1_xboole_0))
% 0.37/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('13', plain, (((sk_C) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('14', plain, (((sk_D) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)],
% 0.37/0.56                ['10', '11', '12', '13', '14'])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X23 @ sk_B)
% 0.37/0.56          | ~ (m1_subset_1 @ X24 @ sk_D)
% 0.37/0.56          | ((sk_F_1) != (k4_mcart_1 @ X25 @ X23 @ X26 @ X24))
% 0.37/0.56          | ((sk_E) = (X23))
% 0.37/0.56          | ~ (m1_subset_1 @ X26 @ sk_C)
% 0.37/0.56          | ~ (m1_subset_1 @ X25 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.37/0.56          | ((sk_E) = (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.37/0.56          | ((sk_F_1)
% 0.37/0.56              != (k4_mcart_1 @ X0 @ 
% 0.37/0.56                  (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ X1 @ X2))
% 0.37/0.56          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.37/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      ((((sk_F_1) != (sk_F_1))
% 0.37/0.56        | ~ (m1_subset_1 @ (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.37/0.56        | ((sk_E) = (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.37/0.56        | ~ (m1_subset_1 @ (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.37/0.56        | ~ (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['7', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (((X10) = (k1_xboole_0))
% 0.37/0.56          | ((X11) = (k1_xboole_0))
% 0.37/0.56          | ((X12) = (k1_xboole_0))
% 0.37/0.56          | (m1_subset_1 @ (sk_I_1 @ X13 @ X14 @ X12 @ X11 @ X10) @ X14)
% 0.37/0.56          | ~ (m1_subset_1 @ X13 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14))
% 0.37/0.56          | ((X14) = (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      ((((sk_D) = (k1_xboole_0))
% 0.37/0.56        | (m1_subset_1 @ (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.37/0.56        | ((sk_C) = (k1_xboole_0))
% 0.37/0.56        | ((sk_B) = (k1_xboole_0))
% 0.37/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.56  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('25', plain, (((sk_D) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)],
% 0.37/0.56                ['21', '22', '23', '24', '25'])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (((X10) = (k1_xboole_0))
% 0.37/0.56          | ((X11) = (k1_xboole_0))
% 0.37/0.56          | ((X12) = (k1_xboole_0))
% 0.37/0.56          | (m1_subset_1 @ (sk_H_1 @ X13 @ X14 @ X12 @ X11 @ X10) @ X12)
% 0.37/0.56          | ~ (m1_subset_1 @ X13 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14))
% 0.37/0.56          | ((X14) = (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      ((((sk_D) = (k1_xboole_0))
% 0.37/0.56        | (m1_subset_1 @ (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.37/0.56        | ((sk_C) = (k1_xboole_0))
% 0.37/0.56        | ((sk_B) = (k1_xboole_0))
% 0.37/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.56  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('31', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('32', plain, (((sk_C) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('33', plain, (((sk_D) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)],
% 0.37/0.56                ['29', '30', '31', '32', '33'])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (((X10) = (k1_xboole_0))
% 0.37/0.56          | ((X11) = (k1_xboole_0))
% 0.37/0.56          | ((X12) = (k1_xboole_0))
% 0.37/0.56          | (m1_subset_1 @ (sk_F @ X13 @ X14 @ X12 @ X11 @ X10) @ X10)
% 0.37/0.56          | ~ (m1_subset_1 @ X13 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X14))
% 0.37/0.56          | ((X14) = (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      ((((sk_D) = (k1_xboole_0))
% 0.37/0.56        | (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.37/0.56        | ((sk_C) = (k1_xboole_0))
% 0.37/0.56        | ((sk_B) = (k1_xboole_0))
% 0.37/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('39', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('40', plain, (((sk_C) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('41', plain, (((sk_D) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)],
% 0.37/0.56                ['37', '38', '39', '40', '41'])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      ((((sk_F_1) != (sk_F_1))
% 0.37/0.56        | ((sk_E) = (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['18', '26', '34', '42'])).
% 0.37/0.56  thf('44', plain, (((sk_E) = (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.37/0.56      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (((sk_F_1)
% 0.37/0.56         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.37/0.56            (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.37/0.56            (sk_H_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.37/0.56            (sk_I_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)],
% 0.37/0.56                ['10', '11', '12', '13', '14'])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d9_mcart_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.56          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.37/0.56          ( ~( ![E:$i]:
% 0.37/0.56               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.37/0.56                 ( ![F:$i]:
% 0.37/0.56                   ( ( m1_subset_1 @ F @ B ) =>
% 0.37/0.56                     ( ( ( F ) = ( k9_mcart_1 @ A @ B @ C @ D @ E ) ) <=>
% 0.37/0.56                       ( ![G:$i,H:$i,I:$i,J:$i]:
% 0.37/0.56                         ( ( ( E ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.37/0.56                           ( ( F ) = ( H ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         (((X0) = (k1_xboole_0))
% 0.37/0.56          | ((X1) = (k1_xboole_0))
% 0.37/0.56          | ((X2) = (k1_xboole_0))
% 0.37/0.56          | ~ (m1_subset_1 @ X3 @ X1)
% 0.37/0.56          | ((X4)
% 0.37/0.56              = (k4_mcart_1 @ (sk_G @ X3 @ X4) @ (sk_H @ X3 @ X4) @ 
% 0.37/0.56                 (sk_I @ X3 @ X4) @ (sk_J @ X3 @ X4)))
% 0.37/0.56          | ((X3) = (k9_mcart_1 @ X0 @ X1 @ X2 @ X5 @ X4))
% 0.37/0.56          | ~ (m1_subset_1 @ X4 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X5))
% 0.37/0.56          | ((X5) = (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d9_mcart_1])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((sk_D) = (k1_xboole_0))
% 0.37/0.56          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56          | ((sk_F_1)
% 0.37/0.56              = (k4_mcart_1 @ (sk_G @ X0 @ sk_F_1) @ (sk_H @ X0 @ sk_F_1) @ 
% 0.37/0.56                 (sk_I @ X0 @ sk_F_1) @ (sk_J @ X0 @ sk_F_1)))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.37/0.56          | ((sk_C) = (k1_xboole_0))
% 0.37/0.56          | ((sk_B) = (k1_xboole_0))
% 0.37/0.56          | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.56  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('51', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('52', plain, (((sk_C) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('53', plain, (((sk_D) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56          | ((sk_F_1)
% 0.37/0.56              = (k4_mcart_1 @ (sk_G @ X0 @ sk_F_1) @ (sk_H @ X0 @ sk_F_1) @ 
% 0.37/0.56                 (sk_I @ X0 @ sk_F_1) @ (sk_J @ X0 @ sk_F_1)))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)],
% 0.37/0.56                ['49', '50', '51', '52', '53'])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      ((((sk_F_1)
% 0.37/0.56          = (k4_mcart_1 @ 
% 0.37/0.56             (sk_G @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_H @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_I @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_J @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1)))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['46', '54'])).
% 0.37/0.56  thf(t33_mcart_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.37/0.56     ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.37/0.56       ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.37/0.56         ( ( D ) = ( H ) ) ) ))).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, 
% 0.37/0.56         X22 : $i]:
% 0.37/0.56         (((X20) = (X17))
% 0.37/0.56          | ((k4_mcart_1 @ X16 @ X20 @ X21 @ X22)
% 0.37/0.56              != (k4_mcart_1 @ X15 @ X17 @ X18 @ X19)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t33_mcart_1])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (![X16 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.56         (('#_fresh_sk2' @ (k4_mcart_1 @ X16 @ X20 @ X21 @ X22)) = (X20))),
% 0.37/0.56      inference('inj_rec', [status(thm)], ['56'])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (((('#_fresh_sk2' @ sk_F_1)
% 0.37/0.56          = (sk_H @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['55', '57'])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      ((((sk_F_1)
% 0.37/0.56          = (k4_mcart_1 @ 
% 0.37/0.56             (sk_G @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_H @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_I @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_J @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1)))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['46', '54'])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, 
% 0.37/0.56         X22 : $i]:
% 0.37/0.56         (((X16) = (X15))
% 0.37/0.56          | ((k4_mcart_1 @ X16 @ X20 @ X21 @ X22)
% 0.37/0.56              != (k4_mcart_1 @ X15 @ X17 @ X18 @ X19)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t33_mcart_1])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (![X16 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.56         (('#_fresh_sk1' @ (k4_mcart_1 @ X16 @ X20 @ X21 @ X22)) = (X16))),
% 0.37/0.56      inference('inj_rec', [status(thm)], ['60'])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (((('#_fresh_sk1' @ sk_F_1)
% 0.37/0.56          = (sk_G @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['59', '61'])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      ((((sk_F_1)
% 0.37/0.56          = (k4_mcart_1 @ 
% 0.37/0.56             (sk_G @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_H @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_I @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_J @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1)))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['46', '54'])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      ((((sk_F_1)
% 0.37/0.56          = (k4_mcart_1 @ ('#_fresh_sk1' @ sk_F_1) @ 
% 0.37/0.56             (sk_H @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_I @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_J @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1)))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['62', '63'])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      ((((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56          = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56        | ((sk_F_1)
% 0.37/0.56            = (k4_mcart_1 @ ('#_fresh_sk1' @ sk_F_1) @ 
% 0.37/0.56               (sk_H @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56               (sk_I @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56               (sk_J @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['64'])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      ((((sk_F_1)
% 0.37/0.56          = (k4_mcart_1 @ ('#_fresh_sk1' @ sk_F_1) @ 
% 0.37/0.56             ('#_fresh_sk2' @ sk_F_1) @ 
% 0.37/0.56             (sk_I @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56             (sk_J @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1)))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['58', '65'])).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      ((((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56          = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56        | ((sk_F_1)
% 0.37/0.56            = (k4_mcart_1 @ ('#_fresh_sk1' @ sk_F_1) @ 
% 0.37/0.56               ('#_fresh_sk2' @ sk_F_1) @ 
% 0.37/0.56               (sk_I @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1) @ 
% 0.37/0.56               (sk_J @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['66'])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, 
% 0.37/0.56         X22 : $i]:
% 0.37/0.56         (((X20) = (X17))
% 0.37/0.56          | ((k4_mcart_1 @ X16 @ X20 @ X21 @ X22)
% 0.37/0.56              != (k4_mcart_1 @ X15 @ X17 @ X18 @ X19)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t33_mcart_1])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         (((k4_mcart_1 @ X3 @ X2 @ X1 @ X0) != (sk_F_1))
% 0.37/0.56          | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56              = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56          | ((X2) = ('#_fresh_sk2' @ sk_F_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.56  thf('70', plain,
% 0.37/0.56      ((((sk_F_1) != (sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = ('#_fresh_sk2' @ sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '69'])).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      ((((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56          = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = ('#_fresh_sk2' @ sk_F_1)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['70'])).
% 0.37/0.56  thf('72', plain, (((sk_E) = (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.37/0.56      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      ((((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56          = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56        | ((sk_E) = ('#_fresh_sk2' @ sk_F_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['71', '72'])).
% 0.37/0.56  thf('74', plain,
% 0.37/0.56      (((('#_fresh_sk2' @ sk_F_1)
% 0.37/0.56          = (sk_H @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['55', '57'])).
% 0.37/0.56  thf('75', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)],
% 0.37/0.56                ['10', '11', '12', '13', '14'])).
% 0.37/0.56  thf('76', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('77', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         (((X0) = (k1_xboole_0))
% 0.37/0.56          | ((X1) = (k1_xboole_0))
% 0.37/0.56          | ((X2) = (k1_xboole_0))
% 0.37/0.56          | ~ (m1_subset_1 @ X3 @ X1)
% 0.37/0.56          | ((X3) != (sk_H @ X3 @ X4))
% 0.37/0.56          | ((X3) = (k9_mcart_1 @ X0 @ X1 @ X2 @ X5 @ X4))
% 0.37/0.56          | ~ (m1_subset_1 @ X4 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X5))
% 0.37/0.56          | ((X5) = (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d9_mcart_1])).
% 0.37/0.56  thf('78', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((sk_D) = (k1_xboole_0))
% 0.37/0.56          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56          | ((X0) != (sk_H @ X0 @ sk_F_1))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.37/0.56          | ((sk_C) = (k1_xboole_0))
% 0.37/0.56          | ((sk_B) = (k1_xboole_0))
% 0.37/0.56          | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['76', '77'])).
% 0.37/0.56  thf('79', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('80', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('81', plain, (((sk_C) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('82', plain, (((sk_D) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('83', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56          | ((X0) != (sk_H @ X0 @ sk_F_1))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)],
% 0.37/0.56                ['78', '79', '80', '81', '82'])).
% 0.37/0.56  thf('84', plain,
% 0.37/0.56      ((((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56          != (sk_H @ (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['75', '83'])).
% 0.37/0.56  thf('85', plain,
% 0.37/0.56      ((((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56          != ('#_fresh_sk2' @ sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['74', '84'])).
% 0.37/0.56  thf('86', plain,
% 0.37/0.56      ((((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56          = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56        | ((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56            != ('#_fresh_sk2' @ sk_F_1)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['85'])).
% 0.37/0.56  thf('87', plain, (((sk_E) = (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.37/0.56      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.56  thf('88', plain, (((sk_E) = (sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.37/0.56      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.56  thf('89', plain,
% 0.37/0.56      ((((sk_E) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))
% 0.37/0.56        | ((sk_E) != ('#_fresh_sk2' @ sk_F_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.37/0.56  thf('90', plain,
% 0.37/0.56      (((sk_E) != (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('91', plain, (((sk_E) != ('#_fresh_sk2' @ sk_F_1))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 0.37/0.56  thf('92', plain,
% 0.37/0.56      (((sk_G_1 @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.37/0.56         = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['73', '91'])).
% 0.37/0.56  thf('93', plain,
% 0.37/0.56      (((sk_E) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.37/0.56      inference('sup+', [status(thm)], ['44', '92'])).
% 0.37/0.56  thf('94', plain,
% 0.37/0.56      (((sk_E) != (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('95', plain, ($false),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
