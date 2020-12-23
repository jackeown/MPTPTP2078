%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bqIXrkt5fv

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 752 expanded)
%              Number of leaves         :   24 ( 235 expanded)
%              Depth                    :   20
%              Number of atoms          : 1945 (24762 expanded)
%              Number of equality atoms :  249 (3509 expanded)
%              Maximal formula depth    :   27 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_J_type,type,(
    sk_J: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t81_mcart_1,conjecture,(
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
                         => ( E = I ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

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
                           => ( E = I ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_mcart_1,axiom,(
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

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25 ) )
      | ( X27
        = ( k9_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26 ) )
      | ( m1_subset_1 @ ( sk_I @ X26 @ X27 @ X25 @ X24 @ X23 @ X22 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) )
                & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ E ) ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X11 ) ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('5',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25 ) )
      | ( X27
        = ( k9_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26 ) )
      | ( m1_subset_1 @ ( sk_G @ X26 @ X27 @ X25 @ X24 @ X23 @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22','23'])).

thf('25',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25 ) )
      | ( X27
        = ( k9_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26 ) )
      | ( X26
        = ( k4_mcart_1 @ ( sk_G @ X26 @ X27 @ X25 @ X24 @ X23 @ X22 ) @ ( sk_H @ X26 @ X27 @ X25 @ X24 @ X23 @ X22 ) @ ( sk_I @ X26 @ X27 @ X25 @ X24 @ X23 @ X22 ) @ ( sk_J @ X26 @ X27 @ X25 @ X24 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25 ) )
      | ( X27
        = ( k9_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26 ) )
      | ( m1_subset_1 @ ( sk_H @ X26 @ X27 @ X25 @ X24 @ X23 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['41','42','43','44','45'])).

thf('47',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ sk_B )
      | ~ ( m1_subset_1 @ X29 @ sk_D )
      | ( sk_F
       != ( k4_mcart_1 @ X30 @ X28 @ X31 @ X29 ) )
      | ( sk_E = X31 )
      | ~ ( m1_subset_1 @ X31 @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ sk_C )
      | ( sk_E = X2 )
      | ( sk_F
       != ( k4_mcart_1 @ X1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_F != sk_F )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25 ) )
      | ( X27
        = ( k9_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26 ) )
      | ( m1_subset_1 @ ( sk_J @ X26 @ X27 @ X25 @ X24 @ X23 @ X22 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['54','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34','35'])).

thf('67',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34','35'])).

thf(t78_mcart_1,axiom,(
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

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X16 @ X15 @ X14 @ X13 ) )
      | ( ( k10_mcart_1 @ X16 @ X15 @ X14 @ X13 @ X17 )
        = X21 )
      | ( X17
       != ( k4_mcart_1 @ X19 @ X20 @ X21 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t78_mcart_1])).

thf('70',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( k10_mcart_1 @ X16 @ X15 @ X14 @ X13 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X18 ) )
        = X21 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X18 ) @ ( k4_zfmisc_1 @ X16 @ X15 @ X14 @ X13 ) )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_I @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['72','73','74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup+',[status(thm)],['66','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('81',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) )
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(demod,[status(thm)],['78','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) )
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) )
        = sk_E )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup+',[status(thm)],['65','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) )
        = sk_E ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    sk_E
 != ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['81','82','83','84','85'])).

thf('93',plain,(
    sk_E
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['90','93'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] : ( X1 = X0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_E
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('98',plain,(
    ! [X0: $i] : ( sk_E != X0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference(simplify,[status(thm)],['98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bqIXrkt5fv
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:37:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 63 iterations in 0.079s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.52  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_J_type, type, sk_J: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.52  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.52  thf(t81_mcart_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.52       ( ( ![G:$i]:
% 0.20/0.52           ( ( m1_subset_1 @ G @ A ) =>
% 0.20/0.52             ( ![H:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ H @ B ) =>
% 0.20/0.52                 ( ![I:$i]:
% 0.20/0.52                   ( ( m1_subset_1 @ I @ C ) =>
% 0.20/0.52                     ( ![J:$i]:
% 0.20/0.52                       ( ( m1_subset_1 @ J @ D ) =>
% 0.20/0.52                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.20/0.52                           ( ( E ) = ( I ) ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.52         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52           ( ( E ) = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.52          ( ( ![G:$i]:
% 0.20/0.52              ( ( m1_subset_1 @ G @ A ) =>
% 0.20/0.52                ( ![H:$i]:
% 0.20/0.52                  ( ( m1_subset_1 @ H @ B ) =>
% 0.20/0.52                    ( ![I:$i]:
% 0.20/0.52                      ( ( m1_subset_1 @ I @ C ) =>
% 0.20/0.52                        ( ![J:$i]:
% 0.20/0.52                          ( ( m1_subset_1 @ J @ D ) =>
% 0.20/0.52                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.20/0.52                              ( ( E ) = ( I ) ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.52            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52              ( ( E ) = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t81_mcart_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t80_mcart_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.52       ( ( ![G:$i]:
% 0.20/0.52           ( ( m1_subset_1 @ G @ A ) =>
% 0.20/0.52             ( ![H:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ H @ B ) =>
% 0.20/0.52                 ( ![I:$i]:
% 0.20/0.52                   ( ( m1_subset_1 @ I @ C ) =>
% 0.20/0.52                     ( ![J:$i]:
% 0.20/0.52                       ( ( m1_subset_1 @ J @ D ) =>
% 0.20/0.52                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.20/0.52                           ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.52         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52           ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.52         (((X22) = (k1_xboole_0))
% 0.20/0.52          | ((X23) = (k1_xboole_0))
% 0.20/0.52          | ((X24) = (k1_xboole_0))
% 0.20/0.52          | ((X25) = (k1_xboole_0))
% 0.20/0.52          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25))
% 0.20/0.52          | ((X27) = (k9_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26))
% 0.20/0.52          | (m1_subset_1 @ (sk_I @ X26 @ X27 @ X25 @ X24 @ X23 @ X22) @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.52          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.20/0.52          | ((sk_D) = (k1_xboole_0))
% 0.20/0.52          | ((sk_C) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t61_mcart_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ~( ![E:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.52                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.52                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.52                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.52                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.52                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.52                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.20/0.52                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         (((X8) = (k1_xboole_0))
% 0.20/0.52          | ((X9) = (k1_xboole_0))
% 0.20/0.52          | ((X10) = (k1_xboole_0))
% 0.20/0.52          | ((k9_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11)
% 0.20/0.52              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X11))))
% 0.20/0.52          | ~ (m1_subset_1 @ X11 @ (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12))
% 0.20/0.52          | ((X12) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      ((((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52        | ((sk_C) = (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((sk_D) = (k1_xboole_0))
% 0.20/0.52          | ((sk_C) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '10'])).
% 0.20/0.52  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('15', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)],
% 0.20/0.52                ['11', '12', '13', '14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.52         (((X22) = (k1_xboole_0))
% 0.20/0.52          | ((X23) = (k1_xboole_0))
% 0.20/0.52          | ((X24) = (k1_xboole_0))
% 0.20/0.52          | ((X25) = (k1_xboole_0))
% 0.20/0.52          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25))
% 0.20/0.52          | ((X27) = (k9_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26))
% 0.20/0.52          | (m1_subset_1 @ (sk_G @ X26 @ X27 @ X25 @ X24 @ X23 @ X22) @ X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.52          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.20/0.52          | ((sk_D) = (k1_xboole_0))
% 0.20/0.52          | ((sk_C) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('21', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('23', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.52          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)],
% 0.20/0.52                ['19', '20', '21', '22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.52         (((X22) = (k1_xboole_0))
% 0.20/0.52          | ((X23) = (k1_xboole_0))
% 0.20/0.52          | ((X24) = (k1_xboole_0))
% 0.20/0.52          | ((X25) = (k1_xboole_0))
% 0.20/0.52          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25))
% 0.20/0.52          | ((X27) = (k9_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26))
% 0.20/0.52          | ((X26)
% 0.20/0.52              = (k4_mcart_1 @ (sk_G @ X26 @ X27 @ X25 @ X24 @ X23 @ X22) @ 
% 0.20/0.52                 (sk_H @ X26 @ X27 @ X25 @ X24 @ X23 @ X22) @ 
% 0.20/0.52                 (sk_I @ X26 @ X27 @ X25 @ X24 @ X23 @ X22) @ 
% 0.20/0.52                 (sk_J @ X26 @ X27 @ X25 @ X24 @ X23 @ X22))))),
% 0.20/0.52      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((sk_F)
% 0.20/0.52            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.52          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.20/0.52          | ((sk_D) = (k1_xboole_0))
% 0.20/0.52          | ((sk_C) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((sk_F)
% 0.20/0.52            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((sk_D) = (k1_xboole_0))
% 0.20/0.52          | ((sk_C) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('35', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((sk_F)
% 0.20/0.52            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)],
% 0.20/0.52                ['31', '32', '33', '34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.52         (((X22) = (k1_xboole_0))
% 0.20/0.52          | ((X23) = (k1_xboole_0))
% 0.20/0.52          | ((X24) = (k1_xboole_0))
% 0.20/0.52          | ((X25) = (k1_xboole_0))
% 0.20/0.52          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25))
% 0.20/0.52          | ((X27) = (k9_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26))
% 0.20/0.52          | (m1_subset_1 @ (sk_H @ X26 @ X27 @ X25 @ X24 @ X23 @ X22) @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.52          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.20/0.52          | ((sk_D) = (k1_xboole_0))
% 0.20/0.52          | ((sk_C) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((sk_D) = (k1_xboole_0))
% 0.20/0.52          | ((sk_C) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('43', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('44', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)],
% 0.20/0.52                ['41', '42', '43', '44', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.52          | ~ (m1_subset_1 @ X29 @ sk_D)
% 0.20/0.52          | ((sk_F) != (k4_mcart_1 @ X30 @ X28 @ X31 @ X29))
% 0.20/0.52          | ((sk_E) = (X31))
% 0.20/0.52          | ~ (m1_subset_1 @ X31 @ sk_C)
% 0.20/0.52          | ~ (m1_subset_1 @ X30 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ sk_C)
% 0.20/0.52          | ((sk_E) = (X2))
% 0.20/0.52          | ((sk_F)
% 0.20/0.52              != (k4_mcart_1 @ X1 @ 
% 0.20/0.52                  (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ X2 @ X3))
% 0.20/0.52          | ~ (m1_subset_1 @ X3 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((sk_F) != (sk_F))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               sk_D)
% 0.20/0.52          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               sk_C)
% 0.20/0.52          | ~ (m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               sk_A)
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52             sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               sk_C)
% 0.20/0.52          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               sk_D)
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               sk_D)
% 0.20/0.52          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52             sk_C)
% 0.20/0.52          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               sk_D)
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               sk_D)
% 0.20/0.52          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '52'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               sk_D)
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.52         (((X22) = (k1_xboole_0))
% 0.20/0.52          | ((X23) = (k1_xboole_0))
% 0.20/0.52          | ((X24) = (k1_xboole_0))
% 0.20/0.52          | ((X25) = (k1_xboole_0))
% 0.20/0.52          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25))
% 0.20/0.52          | ((X27) = (k9_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26))
% 0.20/0.52          | (m1_subset_1 @ (sk_J @ X26 @ X27 @ X25 @ X24 @ X23 @ X22) @ X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.20/0.52          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.20/0.52          | ((sk_D) = (k1_xboole_0))
% 0.20/0.52          | ((sk_C) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((sk_D) = (k1_xboole_0))
% 0.20/0.52          | ((sk_C) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.52  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('61', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('62', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('63', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)],
% 0.20/0.52                ['59', '60', '61', '62', '63'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['54', '64'])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((sk_F)
% 0.20/0.52            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)],
% 0.20/0.52                ['31', '32', '33', '34', '35'])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((sk_F)
% 0.20/0.52            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)],
% 0.20/0.52                ['31', '32', '33', '34', '35'])).
% 0.20/0.52  thf(t78_mcart_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.52       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.20/0.52              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.20/0.52                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.20/0.52                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.20/0.52                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.20/0.52                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, 
% 0.20/0.52         X20 : $i, X21 : $i]:
% 0.20/0.52         (((X13) = (k1_xboole_0))
% 0.20/0.52          | ((X14) = (k1_xboole_0))
% 0.20/0.52          | ((X15) = (k1_xboole_0))
% 0.20/0.52          | ((X16) = (k1_xboole_0))
% 0.20/0.52          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X16 @ X15 @ X14 @ X13))
% 0.20/0.52          | ((k10_mcart_1 @ X16 @ X15 @ X14 @ X13 @ X17) = (X21))
% 0.20/0.52          | ((X17) != (k4_mcart_1 @ X19 @ X20 @ X21 @ X18)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t78_mcart_1])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.20/0.52         X21 : $i]:
% 0.20/0.52         (((k10_mcart_1 @ X16 @ X15 @ X14 @ X13 @ 
% 0.20/0.52            (k4_mcart_1 @ X19 @ X20 @ X21 @ X18)) = (X21))
% 0.20/0.52          | ~ (m1_subset_1 @ (k4_mcart_1 @ X19 @ X20 @ X21 @ X18) @ 
% 0.20/0.52               (k4_zfmisc_1 @ X16 @ X15 @ X14 @ X13))
% 0.20/0.52          | ((X16) = (k1_xboole_0))
% 0.20/0.52          | ((X15) = (k1_xboole_0))
% 0.20/0.52          | ((X14) = (k1_xboole_0))
% 0.20/0.52          | ((X13) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.52          | ((X4) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ((X2) = (k1_xboole_0))
% 0.20/0.52          | ((X3) = (k1_xboole_0))
% 0.20/0.52          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.20/0.52              (k4_mcart_1 @ (sk_G @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_H @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_I @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52               (sk_J @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.52              = (sk_I @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['68', '70'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 0.20/0.52            (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52             (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52             (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52             (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.52            = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ((sk_A) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ((sk_C) = (k1_xboole_0))
% 0.20/0.52          | ((sk_D) = (k1_xboole_0))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['67', '71'])).
% 0.20/0.52  thf('73', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('74', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('75', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('76', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 0.20/0.52            (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52             (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52             (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52             (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.52            = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)],
% 0.20/0.52                ['72', '73', '74', '75', '76'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52            = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['66', '77'])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         (((X8) = (k1_xboole_0))
% 0.20/0.52          | ((X9) = (k1_xboole_0))
% 0.20/0.52          | ((X10) = (k1_xboole_0))
% 0.20/0.52          | ((k10_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11)
% 0.20/0.52              = (k2_mcart_1 @ (k1_mcart_1 @ X11)))
% 0.20/0.52          | ~ (m1_subset_1 @ X11 @ (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12))
% 0.20/0.52          | ((X12) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      ((((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52            = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.20/0.52        | ((sk_C) = (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.52  thf('82', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('83', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('84', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('85', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)],
% 0.20/0.52                ['81', '82', '83', '84', '85'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k2_mcart_1 @ (k1_mcart_1 @ sk_F))
% 0.20/0.52            = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['78', '86'])).
% 0.20/0.52  thf('88', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_F))
% 0.20/0.52              = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['87'])).
% 0.20/0.52  thf('89', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k2_mcart_1 @ (k1_mcart_1 @ sk_F)) = (sk_E))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['65', '88'])).
% 0.20/0.52  thf('90', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.52          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_F)) = (sk_E)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['89'])).
% 0.20/0.52  thf('91', plain,
% 0.20/0.52      (((sk_E) != (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('92', plain,
% 0.20/0.52      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)],
% 0.20/0.52                ['81', '82', '83', '84', '85'])).
% 0.20/0.52  thf('93', plain, (((sk_E) != (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.20/0.52      inference('demod', [status(thm)], ['91', '92'])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      (![X0 : $i]: ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['90', '93'])).
% 0.20/0.52  thf('95', plain,
% 0.20/0.52      (![X0 : $i]: ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['90', '93'])).
% 0.20/0.52  thf('96', plain, (![X0 : $i, X1 : $i]: ((X1) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['94', '95'])).
% 0.20/0.52  thf('97', plain, (((sk_E) != (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.20/0.52      inference('demod', [status(thm)], ['91', '92'])).
% 0.20/0.52  thf('98', plain, (![X0 : $i]: ((sk_E) != (X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.52  thf('99', plain, ($false), inference('simplify', [status(thm)], ['98'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
