%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GOD2NZKlBy

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:11 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  169 (2253 expanded)
%              Number of leaves         :   32 ( 726 expanded)
%              Depth                    :   30
%              Number of atoms          : 2657 (51489 expanded)
%              Number of equality atoms :  324 (6608 expanded)
%              Maximal formula depth    :   27 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_J_type,type,(
    sk_J: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t79_mcart_1,axiom,(
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

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X32 @ ( k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31 ) )
      | ( X33
        = ( k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32 ) )
      | ( m1_subset_1 @ ( sk_I @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t79_mcart_1])).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X32 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 @ X31 ) )
      | ( X33
        = ( k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32 ) )
      | ( m1_subset_1 @ ( sk_I @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ X30 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

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

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X23 @ X24 @ X25 @ X27 @ X26 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X23 @ X24 @ X25 @ X27 @ X26 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X32 @ ( k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31 ) )
      | ( X33
        = ( k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32 ) )
      | ( m1_subset_1 @ ( sk_G @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t79_mcart_1])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('32',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X32 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 @ X31 ) )
      | ( X33
        = ( k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32 ) )
      | ( m1_subset_1 @ ( sk_G @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ X28 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23','24','25','26'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X32 @ ( k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31 ) )
      | ( X33
        = ( k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32 ) )
      | ( X32
        = ( k4_mcart_1 @ ( sk_G @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ ( sk_H @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ ( sk_I @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ ( sk_J @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t79_mcart_1])).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X32 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 @ X31 ) )
      | ( X33
        = ( k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32 ) )
      | ( X32
        = ( k3_mcart_1 @ ( k4_tarski @ ( sk_G @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ ( sk_H @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) ) @ ( sk_I @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ ( sk_J @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k3_mcart_1 @ ( k4_tarski @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23','24','25','26'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k3_mcart_1 @ ( k4_tarski @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k3_mcart_1 @ ( k4_tarski @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('59',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X32 @ ( k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31 ) )
      | ( X33
        = ( k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32 ) )
      | ( m1_subset_1 @ ( sk_H @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t79_mcart_1])).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('61',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X32 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 @ X31 ) )
      | ( X33
        = ( k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32 ) )
      | ( m1_subset_1 @ ( sk_H @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ X29 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23','24','25','26'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65','66','67','68'])).

thf('70',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ sk_B )
      | ~ ( m1_subset_1 @ X35 @ sk_D )
      | ( sk_F
       != ( k4_mcart_1 @ X36 @ X34 @ X37 @ X35 ) )
      | ( sk_E = X34 )
      | ~ ( m1_subset_1 @ X37 @ sk_C )
      | ~ ( m1_subset_1 @ X36 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('72',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ sk_B )
      | ~ ( m1_subset_1 @ X35 @ sk_D )
      | ( sk_F
       != ( k3_mcart_1 @ ( k4_tarski @ X36 @ X34 ) @ X37 @ X35 ) )
      | ( sk_E = X34 )
      | ~ ( m1_subset_1 @ X37 @ sk_C )
      | ~ ( m1_subset_1 @ X36 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ sk_C )
      | ( sk_E
        = ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( sk_F
       != ( k3_mcart_1 @ ( k4_tarski @ X1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_F != sk_F )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup-',[status(thm)],['57','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_E
        = ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_E
        = ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('81',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X32 @ ( k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31 ) )
      | ( X33
        = ( k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32 ) )
      | ( m1_subset_1 @ ( sk_J @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t79_mcart_1])).

thf('82',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('83',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X32 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 @ X31 ) )
      | ( X33
        = ( k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32 ) )
      | ( m1_subset_1 @ ( sk_J @ X32 @ X33 @ X31 @ X30 @ X29 @ X28 ) @ X31 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23','24','25','26'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87','88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_E
        = ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['79','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k3_mcart_1 @ ( k4_tarski @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53','54','55','56'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k3_mcart_1 @ ( k4_tarski @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_F
        = ( k3_mcart_1 @ ( k4_tarski @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_F
        = ( k3_mcart_1 @ ( k4_tarski @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf(t59_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ? [E: $i] :
            ( ? [F: $i,G: $i,H: $i,I: $i] :
                ( ~ ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                      = F )
                    & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                      = G )
                    & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                      = H )
                    & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                      = I ) )
                & ( E
                  = ( k4_mcart_1 @ F @ G @ H @ I ) ) )
            & ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) )).

thf('98',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X21
       != ( k4_mcart_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( ( k9_mcart_1 @ X14 @ X15 @ X16 @ X22 @ X21 )
        = X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('99',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X17 @ X18 @ X19 @ X20 ) @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X22 ) )
      | ( ( k9_mcart_1 @ X14 @ X15 @ X16 @ X22 @ ( k4_mcart_1 @ X17 @ X18 @ X19 @ X20 ) )
        = X18 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('101',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('102',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('103',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k4_tarski @ X17 @ X18 ) @ X19 @ X20 ) @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 @ X22 ) )
      | ( ( k9_mcart_1 @ X14 @ X15 @ X16 @ X22 @ ( k3_mcart_1 @ ( k4_tarski @ X17 @ X18 ) @ X19 @ X20 ) )
        = X18 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) )
      | ( X4
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( k4_tarski @ ( sk_G @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) @ ( sk_I @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = sk_E )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k3_mcart_1 @ ( k4_tarski @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = sk_E )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup-',[status(thm)],['96','104'])).

thf('106',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k3_mcart_1 @ ( k4_tarski @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = sk_E )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = sk_E )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup+',[status(thm)],['95','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = sk_E ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = sk_E ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('114',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
     != sk_E )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = sk_E ) ),
    inference(eq_fact,[status(thm)],['113'])).

thf('115',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('116',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X23 @ X24 @ X25 @ X27 @ X26 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('117',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('118',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X23 @ X24 @ X25 @ X27 @ X26 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['119','120','121','122','123'])).

thf('125',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
     != sk_E )
    | ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      = sk_E ) ),
    inference(demod,[status(thm)],['114','124'])).

thf('126',plain,(
    sk_E
 != ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['119','120','121','122','123'])).

thf('128',plain,(
    sk_E
 != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
 != sk_E ),
    inference('simplify_reflect-',[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_E )
      | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = sk_E ) ) ),
    inference('sup-',[status(thm)],['112','129'])).

thf('131',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['119','120','121','122','123'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_E )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
        = sk_E ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
    = sk_E ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    sk_E
 != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('135',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['133','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GOD2NZKlBy
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.53/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.72  % Solved by: fo/fo7.sh
% 0.53/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.72  % done 120 iterations in 0.264s
% 0.53/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.72  % SZS output start Refutation
% 0.53/0.72  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.53/0.72  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.53/0.72  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i > $i).
% 0.53/0.72  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.53/0.72  thf(sk_F_type, type, sk_F: $i).
% 0.53/0.72  thf(sk_J_type, type, sk_J: $i > $i > $i > $i > $i > $i > $i).
% 0.53/0.72  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.53/0.72  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.53/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.72  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.53/0.72  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.53/0.72  thf(sk_E_type, type, sk_E: $i).
% 0.53/0.72  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.53/0.72  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i > $i).
% 0.53/0.72  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.53/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.72  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.53/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.53/0.72  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i > $i).
% 0.53/0.72  thf(t80_mcart_1, conjecture,
% 0.53/0.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.53/0.72       ( ( ![G:$i]:
% 0.53/0.72           ( ( m1_subset_1 @ G @ A ) =>
% 0.53/0.72             ( ![H:$i]:
% 0.53/0.72               ( ( m1_subset_1 @ H @ B ) =>
% 0.53/0.72                 ( ![I:$i]:
% 0.53/0.72                   ( ( m1_subset_1 @ I @ C ) =>
% 0.53/0.72                     ( ![J:$i]:
% 0.53/0.72                       ( ( m1_subset_1 @ J @ D ) =>
% 0.53/0.72                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.53/0.72                           ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.53/0.72         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.72           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.53/0.72           ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.53/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.72    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.72        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.53/0.72          ( ( ![G:$i]:
% 0.53/0.72              ( ( m1_subset_1 @ G @ A ) =>
% 0.53/0.72                ( ![H:$i]:
% 0.53/0.72                  ( ( m1_subset_1 @ H @ B ) =>
% 0.53/0.72                    ( ![I:$i]:
% 0.53/0.72                      ( ( m1_subset_1 @ I @ C ) =>
% 0.53/0.72                        ( ![J:$i]:
% 0.53/0.72                          ( ( m1_subset_1 @ J @ D ) =>
% 0.53/0.72                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.53/0.72                              ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.53/0.72            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.72              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.53/0.72              ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.53/0.72    inference('cnf.neg', [status(esa)], [t80_mcart_1])).
% 0.53/0.72  thf('0', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(d4_zfmisc_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.72     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.53/0.72       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.53/0.72  thf('1', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.72         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.53/0.72           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.53/0.72      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.53/0.72  thf('2', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_F @ 
% 0.53/0.72        (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.53/0.72      inference('demod', [status(thm)], ['0', '1'])).
% 0.53/0.72  thf(d3_zfmisc_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.53/0.72       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.53/0.72  thf('3', plain,
% 0.53/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.53/0.72         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.53/0.72           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.53/0.72      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.53/0.72  thf('4', plain,
% 0.53/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.53/0.72         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.53/0.72           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.53/0.72      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.53/0.72  thf('5', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.72         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.53/0.72           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.53/0.72      inference('sup+', [status(thm)], ['3', '4'])).
% 0.53/0.72  thf('6', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_F @ 
% 0.53/0.72        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.53/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.53/0.72  thf(t79_mcart_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.53/0.72       ( ( ![G:$i]:
% 0.53/0.72           ( ( m1_subset_1 @ G @ A ) =>
% 0.53/0.72             ( ![H:$i]:
% 0.53/0.72               ( ( m1_subset_1 @ H @ B ) =>
% 0.53/0.72                 ( ![I:$i]:
% 0.53/0.72                   ( ( m1_subset_1 @ I @ C ) =>
% 0.53/0.72                     ( ![J:$i]:
% 0.53/0.72                       ( ( m1_subset_1 @ J @ D ) =>
% 0.53/0.72                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.53/0.72                           ( ( E ) = ( G ) ) ) ) ) ) ) ) ) ) ) =>
% 0.53/0.72         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.72           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.53/0.72           ( ( E ) = ( k8_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.53/0.72  thf('7', plain,
% 0.53/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.72         (((X28) = (k1_xboole_0))
% 0.53/0.72          | ((X29) = (k1_xboole_0))
% 0.53/0.72          | ((X30) = (k1_xboole_0))
% 0.53/0.72          | ((X31) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ X32 @ (k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31))
% 0.53/0.72          | ((X33) = (k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32))
% 0.53/0.72          | (m1_subset_1 @ (sk_I @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ X30))),
% 0.53/0.72      inference('cnf', [status(esa)], [t79_mcart_1])).
% 0.53/0.72  thf('8', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.72         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.53/0.72           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.53/0.72      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.53/0.72  thf('9', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.72         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.53/0.72           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.53/0.72      inference('sup+', [status(thm)], ['3', '4'])).
% 0.53/0.72  thf('10', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.72         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.53/0.72           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13))),
% 0.53/0.72      inference('demod', [status(thm)], ['8', '9'])).
% 0.53/0.72  thf('11', plain,
% 0.53/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.72         (((X28) = (k1_xboole_0))
% 0.53/0.72          | ((X29) = (k1_xboole_0))
% 0.53/0.72          | ((X30) = (k1_xboole_0))
% 0.53/0.72          | ((X31) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ X32 @ 
% 0.53/0.72               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30 @ X31))
% 0.53/0.72          | ((X33) = (k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32))
% 0.53/0.72          | (m1_subset_1 @ (sk_I @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ X30))),
% 0.53/0.72      inference('demod', [status(thm)], ['7', '10'])).
% 0.53/0.72  thf('12', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.53/0.72          | ((X0) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.53/0.72          | ((sk_D) = (k1_xboole_0))
% 0.53/0.72          | ((sk_C) = (k1_xboole_0))
% 0.53/0.72          | ((sk_B) = (k1_xboole_0))
% 0.53/0.72          | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['6', '11'])).
% 0.53/0.72  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('16', plain, (((sk_D) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('17', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.53/0.72          | ((X0) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['12', '13', '14', '15', '16'])).
% 0.53/0.72  thf('18', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_F @ 
% 0.53/0.72        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.53/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.53/0.72  thf(t61_mcart_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.53/0.72          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.53/0.72          ( ~( ![E:$i]:
% 0.53/0.72               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.53/0.72                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.53/0.72                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.53/0.72                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.53/0.72                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.53/0.72                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.53/0.72                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.53/0.72                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.53/0.72  thf('19', plain,
% 0.53/0.72      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.53/0.72         (((X23) = (k1_xboole_0))
% 0.53/0.72          | ((X24) = (k1_xboole_0))
% 0.53/0.72          | ((X25) = (k1_xboole_0))
% 0.53/0.72          | ((k8_mcart_1 @ X23 @ X24 @ X25 @ X27 @ X26)
% 0.53/0.72              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X26))))
% 0.53/0.72          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27))
% 0.53/0.72          | ((X27) = (k1_xboole_0)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.53/0.72  thf('20', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.72         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.53/0.72           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13))),
% 0.53/0.72      inference('demod', [status(thm)], ['8', '9'])).
% 0.53/0.72  thf('21', plain,
% 0.53/0.72      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.53/0.72         (((X23) = (k1_xboole_0))
% 0.53/0.72          | ((X24) = (k1_xboole_0))
% 0.53/0.72          | ((X25) = (k1_xboole_0))
% 0.53/0.72          | ((k8_mcart_1 @ X23 @ X24 @ X25 @ X27 @ X26)
% 0.53/0.72              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X26))))
% 0.53/0.72          | ~ (m1_subset_1 @ X26 @ 
% 0.53/0.72               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25 @ X27))
% 0.53/0.72          | ((X27) = (k1_xboole_0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['19', '20'])).
% 0.53/0.72  thf('22', plain,
% 0.53/0.72      ((((sk_D) = (k1_xboole_0))
% 0.53/0.72        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.72            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72        | ((sk_C) = (k1_xboole_0))
% 0.53/0.72        | ((sk_B) = (k1_xboole_0))
% 0.53/0.72        | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['18', '21'])).
% 0.53/0.72  thf('23', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('24', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('25', plain, (((sk_C) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('26', plain, (((sk_D) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('27', plain,
% 0.53/0.72      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.72         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['22', '23', '24', '25', '26'])).
% 0.53/0.72  thf('28', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('demod', [status(thm)], ['17', '27'])).
% 0.53/0.72  thf('29', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_F @ 
% 0.53/0.72        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.53/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.53/0.72  thf('30', plain,
% 0.53/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.72         (((X28) = (k1_xboole_0))
% 0.53/0.72          | ((X29) = (k1_xboole_0))
% 0.53/0.72          | ((X30) = (k1_xboole_0))
% 0.53/0.72          | ((X31) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ X32 @ (k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31))
% 0.53/0.72          | ((X33) = (k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32))
% 0.53/0.72          | (m1_subset_1 @ (sk_G @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ X28))),
% 0.53/0.72      inference('cnf', [status(esa)], [t79_mcart_1])).
% 0.53/0.72  thf('31', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.72         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.53/0.72           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13))),
% 0.53/0.72      inference('demod', [status(thm)], ['8', '9'])).
% 0.53/0.72  thf('32', plain,
% 0.53/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.72         (((X28) = (k1_xboole_0))
% 0.53/0.72          | ((X29) = (k1_xboole_0))
% 0.53/0.72          | ((X30) = (k1_xboole_0))
% 0.53/0.72          | ((X31) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ X32 @ 
% 0.53/0.72               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30 @ X31))
% 0.53/0.72          | ((X33) = (k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32))
% 0.53/0.72          | (m1_subset_1 @ (sk_G @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ X28))),
% 0.53/0.72      inference('demod', [status(thm)], ['30', '31'])).
% 0.53/0.72  thf('33', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.53/0.72          | ((X0) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.53/0.72          | ((sk_D) = (k1_xboole_0))
% 0.53/0.72          | ((sk_C) = (k1_xboole_0))
% 0.53/0.72          | ((sk_B) = (k1_xboole_0))
% 0.53/0.72          | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['29', '32'])).
% 0.53/0.72  thf('34', plain,
% 0.53/0.72      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.72         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['22', '23', '24', '25', '26'])).
% 0.53/0.72  thf('35', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((sk_D) = (k1_xboole_0))
% 0.53/0.72          | ((sk_C) = (k1_xboole_0))
% 0.53/0.72          | ((sk_B) = (k1_xboole_0))
% 0.53/0.72          | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['33', '34'])).
% 0.53/0.72  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('37', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('38', plain, (((sk_C) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('39', plain, (((sk_D) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('40', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['35', '36', '37', '38', '39'])).
% 0.53/0.72  thf('41', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_F @ 
% 0.53/0.72        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.53/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.53/0.72  thf('42', plain,
% 0.53/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.72         (((X28) = (k1_xboole_0))
% 0.53/0.72          | ((X29) = (k1_xboole_0))
% 0.53/0.72          | ((X30) = (k1_xboole_0))
% 0.53/0.72          | ((X31) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ X32 @ (k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31))
% 0.53/0.72          | ((X33) = (k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32))
% 0.53/0.72          | ((X32)
% 0.53/0.72              = (k4_mcart_1 @ (sk_G @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ 
% 0.53/0.72                 (sk_H @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ 
% 0.53/0.72                 (sk_I @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ 
% 0.53/0.72                 (sk_J @ X32 @ X33 @ X31 @ X30 @ X29 @ X28))))),
% 0.53/0.72      inference('cnf', [status(esa)], [t79_mcart_1])).
% 0.53/0.72  thf('43', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.72         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.53/0.72           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13))),
% 0.53/0.72      inference('demod', [status(thm)], ['8', '9'])).
% 0.53/0.72  thf(d4_mcart_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.72     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.53/0.72       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.53/0.72  thf('44', plain,
% 0.53/0.72      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.72         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.53/0.72           = (k4_tarski @ (k3_mcart_1 @ X6 @ X7 @ X8) @ X9))),
% 0.53/0.72      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.53/0.72  thf(d3_mcart_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.53/0.72  thf('45', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.53/0.72           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.53/0.72      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.53/0.72  thf('46', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.53/0.72           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.53/0.72      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.53/0.72  thf('47', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.72         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.53/0.72           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.53/0.72      inference('sup+', [status(thm)], ['45', '46'])).
% 0.53/0.72  thf('48', plain,
% 0.53/0.72      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.72         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.53/0.72           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.53/0.72      inference('demod', [status(thm)], ['44', '47'])).
% 0.53/0.72  thf('49', plain,
% 0.53/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.72         (((X28) = (k1_xboole_0))
% 0.53/0.72          | ((X29) = (k1_xboole_0))
% 0.53/0.72          | ((X30) = (k1_xboole_0))
% 0.53/0.72          | ((X31) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ X32 @ 
% 0.53/0.72               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30 @ X31))
% 0.53/0.72          | ((X33) = (k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32))
% 0.53/0.72          | ((X32)
% 0.53/0.72              = (k3_mcart_1 @ 
% 0.53/0.72                 (k4_tarski @ (sk_G @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ 
% 0.53/0.72                  (sk_H @ X32 @ X33 @ X31 @ X30 @ X29 @ X28)) @ 
% 0.53/0.72                 (sk_I @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ 
% 0.53/0.72                 (sk_J @ X32 @ X33 @ X31 @ X30 @ X29 @ X28))))),
% 0.53/0.72      inference('demod', [status(thm)], ['42', '43', '48'])).
% 0.53/0.72  thf('50', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((sk_F)
% 0.53/0.72            = (k3_mcart_1 @ 
% 0.53/0.72               (k4_tarski @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72                (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.53/0.72               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.53/0.72          | ((X0) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.53/0.72          | ((sk_D) = (k1_xboole_0))
% 0.53/0.72          | ((sk_C) = (k1_xboole_0))
% 0.53/0.72          | ((sk_B) = (k1_xboole_0))
% 0.53/0.72          | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['41', '49'])).
% 0.53/0.72  thf('51', plain,
% 0.53/0.72      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.72         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['22', '23', '24', '25', '26'])).
% 0.53/0.72  thf('52', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((sk_F)
% 0.53/0.72            = (k3_mcart_1 @ 
% 0.53/0.72               (k4_tarski @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72                (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.53/0.72               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((sk_D) = (k1_xboole_0))
% 0.53/0.72          | ((sk_C) = (k1_xboole_0))
% 0.53/0.72          | ((sk_B) = (k1_xboole_0))
% 0.53/0.72          | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['50', '51'])).
% 0.53/0.72  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('54', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('55', plain, (((sk_C) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('56', plain, (((sk_D) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('57', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((sk_F)
% 0.53/0.72            = (k3_mcart_1 @ 
% 0.53/0.72               (k4_tarski @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72                (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.53/0.72               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['52', '53', '54', '55', '56'])).
% 0.53/0.72  thf('58', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_F @ 
% 0.53/0.72        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.53/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.53/0.72  thf('59', plain,
% 0.53/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.72         (((X28) = (k1_xboole_0))
% 0.53/0.72          | ((X29) = (k1_xboole_0))
% 0.53/0.72          | ((X30) = (k1_xboole_0))
% 0.53/0.72          | ((X31) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ X32 @ (k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31))
% 0.53/0.72          | ((X33) = (k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32))
% 0.53/0.72          | (m1_subset_1 @ (sk_H @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ X29))),
% 0.53/0.72      inference('cnf', [status(esa)], [t79_mcart_1])).
% 0.53/0.72  thf('60', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.72         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.53/0.72           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13))),
% 0.53/0.72      inference('demod', [status(thm)], ['8', '9'])).
% 0.53/0.72  thf('61', plain,
% 0.53/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.72         (((X28) = (k1_xboole_0))
% 0.53/0.72          | ((X29) = (k1_xboole_0))
% 0.53/0.72          | ((X30) = (k1_xboole_0))
% 0.53/0.72          | ((X31) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ X32 @ 
% 0.53/0.72               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30 @ X31))
% 0.53/0.72          | ((X33) = (k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32))
% 0.53/0.72          | (m1_subset_1 @ (sk_H @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ X29))),
% 0.53/0.72      inference('demod', [status(thm)], ['59', '60'])).
% 0.53/0.72  thf('62', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.53/0.72          | ((X0) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.53/0.72          | ((sk_D) = (k1_xboole_0))
% 0.53/0.72          | ((sk_C) = (k1_xboole_0))
% 0.53/0.72          | ((sk_B) = (k1_xboole_0))
% 0.53/0.72          | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['58', '61'])).
% 0.53/0.72  thf('63', plain,
% 0.53/0.72      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.72         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['22', '23', '24', '25', '26'])).
% 0.53/0.72  thf('64', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((sk_D) = (k1_xboole_0))
% 0.53/0.72          | ((sk_C) = (k1_xboole_0))
% 0.53/0.72          | ((sk_B) = (k1_xboole_0))
% 0.53/0.72          | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['62', '63'])).
% 0.53/0.72  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('66', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('67', plain, (((sk_C) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('68', plain, (((sk_D) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('69', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['64', '65', '66', '67', '68'])).
% 0.53/0.72  thf('70', plain,
% 0.53/0.72      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ X34 @ sk_B)
% 0.53/0.72          | ~ (m1_subset_1 @ X35 @ sk_D)
% 0.53/0.72          | ((sk_F) != (k4_mcart_1 @ X36 @ X34 @ X37 @ X35))
% 0.53/0.72          | ((sk_E) = (X34))
% 0.53/0.72          | ~ (m1_subset_1 @ X37 @ sk_C)
% 0.53/0.72          | ~ (m1_subset_1 @ X36 @ sk_A))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('71', plain,
% 0.53/0.72      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.72         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.53/0.72           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.53/0.72      inference('demod', [status(thm)], ['44', '47'])).
% 0.53/0.72  thf('72', plain,
% 0.53/0.72      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ X34 @ sk_B)
% 0.53/0.72          | ~ (m1_subset_1 @ X35 @ sk_D)
% 0.53/0.72          | ((sk_F) != (k3_mcart_1 @ (k4_tarski @ X36 @ X34) @ X37 @ X35))
% 0.53/0.72          | ((sk_E) = (X34))
% 0.53/0.72          | ~ (m1_subset_1 @ X37 @ sk_C)
% 0.53/0.72          | ~ (m1_subset_1 @ X36 @ sk_A))),
% 0.53/0.72      inference('demod', [status(thm)], ['70', '71'])).
% 0.53/0.72  thf('73', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.72         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ~ (m1_subset_1 @ X1 @ sk_A)
% 0.53/0.72          | ~ (m1_subset_1 @ X2 @ sk_C)
% 0.53/0.72          | ((sk_E) = (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.53/0.72          | ((sk_F)
% 0.53/0.72              != (k3_mcart_1 @ 
% 0.53/0.72                  (k4_tarski @ X1 @ 
% 0.53/0.72                   (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.53/0.72                  X2 @ X3))
% 0.53/0.72          | ~ (m1_subset_1 @ X3 @ sk_D))),
% 0.53/0.72      inference('sup-', [status(thm)], ['69', '72'])).
% 0.53/0.72  thf('74', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((sk_F) != (sk_F))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               sk_D)
% 0.53/0.72          | ((sk_E) = (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.53/0.72          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               sk_C)
% 0.53/0.72          | ~ (m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               sk_A)
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('sup-', [status(thm)], ['57', '73'])).
% 0.53/0.72  thf('75', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72             sk_A)
% 0.53/0.72          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               sk_C)
% 0.53/0.72          | ((sk_E) = (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.53/0.72          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               sk_D)
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('simplify', [status(thm)], ['74'])).
% 0.53/0.72  thf('76', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               sk_D)
% 0.53/0.72          | ((sk_E) = (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.53/0.72          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               sk_C))),
% 0.53/0.72      inference('sup-', [status(thm)], ['40', '75'])).
% 0.53/0.72  thf('77', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72             sk_C)
% 0.53/0.72          | ((sk_E) = (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.53/0.72          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               sk_D)
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('simplify', [status(thm)], ['76'])).
% 0.53/0.72  thf('78', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               sk_D)
% 0.53/0.72          | ((sk_E) = (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['28', '77'])).
% 0.53/0.72  thf('79', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((sk_E) = (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.53/0.72          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               sk_D)
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('simplify', [status(thm)], ['78'])).
% 0.53/0.72  thf('80', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_F @ 
% 0.53/0.72        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.53/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.53/0.72  thf('81', plain,
% 0.53/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.72         (((X28) = (k1_xboole_0))
% 0.53/0.72          | ((X29) = (k1_xboole_0))
% 0.53/0.72          | ((X30) = (k1_xboole_0))
% 0.53/0.72          | ((X31) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ X32 @ (k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31))
% 0.53/0.72          | ((X33) = (k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32))
% 0.53/0.72          | (m1_subset_1 @ (sk_J @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ X31))),
% 0.53/0.72      inference('cnf', [status(esa)], [t79_mcart_1])).
% 0.53/0.72  thf('82', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.72         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.53/0.72           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13))),
% 0.53/0.72      inference('demod', [status(thm)], ['8', '9'])).
% 0.53/0.72  thf('83', plain,
% 0.53/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.72         (((X28) = (k1_xboole_0))
% 0.53/0.72          | ((X29) = (k1_xboole_0))
% 0.53/0.72          | ((X30) = (k1_xboole_0))
% 0.53/0.72          | ((X31) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ X32 @ 
% 0.53/0.72               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30 @ X31))
% 0.53/0.72          | ((X33) = (k8_mcart_1 @ X28 @ X29 @ X30 @ X31 @ X32))
% 0.53/0.72          | (m1_subset_1 @ (sk_J @ X32 @ X33 @ X31 @ X30 @ X29 @ X28) @ X31))),
% 0.53/0.72      inference('demod', [status(thm)], ['81', '82'])).
% 0.53/0.72  thf('84', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.53/0.72          | ((X0) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.53/0.72          | ((sk_D) = (k1_xboole_0))
% 0.53/0.72          | ((sk_C) = (k1_xboole_0))
% 0.53/0.72          | ((sk_B) = (k1_xboole_0))
% 0.53/0.72          | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['80', '83'])).
% 0.53/0.72  thf('85', plain,
% 0.53/0.72      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.72         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['22', '23', '24', '25', '26'])).
% 0.53/0.72  thf('86', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((sk_D) = (k1_xboole_0))
% 0.53/0.72          | ((sk_C) = (k1_xboole_0))
% 0.53/0.72          | ((sk_B) = (k1_xboole_0))
% 0.53/0.72          | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['84', '85'])).
% 0.53/0.72  thf('87', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('88', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('89', plain, (((sk_C) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('90', plain, (((sk_D) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('91', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['86', '87', '88', '89', '90'])).
% 0.53/0.72  thf('92', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((sk_E) = (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.53/0.72      inference('clc', [status(thm)], ['79', '91'])).
% 0.53/0.72  thf('93', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((sk_F)
% 0.53/0.72            = (k3_mcart_1 @ 
% 0.53/0.72               (k4_tarski @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72                (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.53/0.72               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['52', '53', '54', '55', '56'])).
% 0.53/0.72  thf('94', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((sk_F)
% 0.53/0.72            = (k3_mcart_1 @ 
% 0.53/0.72               (k4_tarski @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72                sk_E) @ 
% 0.53/0.72               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('sup+', [status(thm)], ['92', '93'])).
% 0.53/0.72  thf('95', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((sk_F)
% 0.53/0.72              = (k3_mcart_1 @ 
% 0.53/0.72                 (k4_tarski @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72                  sk_E) @ 
% 0.53/0.72                 (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72                 (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.53/0.72      inference('simplify', [status(thm)], ['94'])).
% 0.53/0.72  thf('96', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_F @ 
% 0.53/0.72        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.53/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.53/0.72  thf('97', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((sk_F)
% 0.53/0.72              = (k3_mcart_1 @ 
% 0.53/0.72                 (k4_tarski @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72                  sk_E) @ 
% 0.53/0.72                 (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72                 (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.53/0.72      inference('simplify', [status(thm)], ['94'])).
% 0.53/0.72  thf(t59_mcart_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.53/0.72          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.53/0.72          ( ?[E:$i]:
% 0.53/0.72            ( ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.53/0.72                ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.53/0.72                       ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.53/0.72                       ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.53/0.72                       ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.53/0.72                  ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) & 
% 0.53/0.72              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.53/0.72  thf('98', plain,
% 0.53/0.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.53/0.72         X21 : $i, X22 : $i]:
% 0.53/0.72         (((X14) = (k1_xboole_0))
% 0.53/0.72          | ((X15) = (k1_xboole_0))
% 0.53/0.72          | ((X16) = (k1_xboole_0))
% 0.53/0.72          | ((X21) != (k4_mcart_1 @ X17 @ X18 @ X19 @ X20))
% 0.53/0.72          | ((k9_mcart_1 @ X14 @ X15 @ X16 @ X22 @ X21) = (X18))
% 0.53/0.72          | ~ (m1_subset_1 @ X21 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X22))
% 0.53/0.72          | ((X22) = (k1_xboole_0)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.53/0.72  thf('99', plain,
% 0.53/0.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.53/0.72         X22 : $i]:
% 0.53/0.72         (((X22) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ (k4_mcart_1 @ X17 @ X18 @ X19 @ X20) @ 
% 0.53/0.72               (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X22))
% 0.53/0.72          | ((k9_mcart_1 @ X14 @ X15 @ X16 @ X22 @ 
% 0.53/0.72              (k4_mcart_1 @ X17 @ X18 @ X19 @ X20)) = (X18))
% 0.53/0.72          | ((X16) = (k1_xboole_0))
% 0.53/0.72          | ((X15) = (k1_xboole_0))
% 0.53/0.72          | ((X14) = (k1_xboole_0)))),
% 0.53/0.72      inference('simplify', [status(thm)], ['98'])).
% 0.53/0.72  thf('100', plain,
% 0.53/0.72      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.72         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.53/0.72           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.53/0.72      inference('demod', [status(thm)], ['44', '47'])).
% 0.53/0.72  thf('101', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.72         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.53/0.72           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13))),
% 0.53/0.72      inference('demod', [status(thm)], ['8', '9'])).
% 0.53/0.72  thf('102', plain,
% 0.53/0.72      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.72         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.53/0.72           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.53/0.72      inference('demod', [status(thm)], ['44', '47'])).
% 0.53/0.72  thf('103', plain,
% 0.53/0.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.53/0.72         X22 : $i]:
% 0.53/0.72         (((X22) = (k1_xboole_0))
% 0.53/0.72          | ~ (m1_subset_1 @ 
% 0.53/0.72               (k3_mcart_1 @ (k4_tarski @ X17 @ X18) @ X19 @ X20) @ 
% 0.53/0.72               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16 @ X22))
% 0.53/0.72          | ((k9_mcart_1 @ X14 @ X15 @ X16 @ X22 @ 
% 0.53/0.72              (k3_mcart_1 @ (k4_tarski @ X17 @ X18) @ X19 @ X20)) = (X18))
% 0.53/0.72          | ((X16) = (k1_xboole_0))
% 0.53/0.72          | ((X15) = (k1_xboole_0))
% 0.53/0.72          | ((X14) = (k1_xboole_0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.53/0.72  thf('104', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ sk_F @ 
% 0.53/0.72             (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))
% 0.53/0.72          | ((X4) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((X3) = (k1_xboole_0))
% 0.53/0.72          | ((X2) = (k1_xboole_0))
% 0.53/0.72          | ((X1) = (k1_xboole_0))
% 0.53/0.72          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.53/0.72              (k3_mcart_1 @ 
% 0.53/0.72               (k4_tarski @ (sk_G @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72                sk_E) @ 
% 0.53/0.72               (sk_I @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               (sk_J @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.53/0.72              = (sk_E))
% 0.53/0.72          | ((X0) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['97', '103'])).
% 0.53/0.72  thf('105', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((sk_D) = (k1_xboole_0))
% 0.53/0.72          | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 0.53/0.72              (k3_mcart_1 @ 
% 0.53/0.72               (k4_tarski @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72                sk_E) @ 
% 0.53/0.72               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.53/0.72              = (sk_E))
% 0.53/0.72          | ((sk_C) = (k1_xboole_0))
% 0.53/0.72          | ((sk_B) = (k1_xboole_0))
% 0.53/0.72          | ((sk_A) = (k1_xboole_0))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('sup-', [status(thm)], ['96', '104'])).
% 0.53/0.72  thf('106', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('107', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('108', plain, (((sk_C) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('109', plain, (((sk_D) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('110', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 0.53/0.72            (k3_mcart_1 @ 
% 0.53/0.72             (k4_tarski @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E) @ 
% 0.53/0.72             (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.53/0.72             (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.53/0.72            = (sk_E))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['105', '106', '107', '108', '109'])).
% 0.53/0.72  thf('111', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.53/0.72      inference('sup+', [status(thm)], ['95', '110'])).
% 0.53/0.72  thf('112', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E)))),
% 0.53/0.72      inference('simplify', [status(thm)], ['111'])).
% 0.53/0.72  thf('113', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72          | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E)))),
% 0.53/0.72      inference('simplify', [status(thm)], ['111'])).
% 0.53/0.72  thf('114', plain,
% 0.53/0.72      ((((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) != (sk_E))
% 0.53/0.72        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E)))),
% 0.53/0.72      inference('eq_fact', [status(thm)], ['113'])).
% 0.53/0.72  thf('115', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_F @ 
% 0.53/0.72        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.53/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.53/0.72  thf('116', plain,
% 0.53/0.72      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.53/0.72         (((X23) = (k1_xboole_0))
% 0.53/0.72          | ((X24) = (k1_xboole_0))
% 0.53/0.72          | ((X25) = (k1_xboole_0))
% 0.53/0.72          | ((k9_mcart_1 @ X23 @ X24 @ X25 @ X27 @ X26)
% 0.53/0.72              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X26))))
% 0.53/0.72          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27))
% 0.53/0.72          | ((X27) = (k1_xboole_0)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.53/0.72  thf('117', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.72         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.53/0.72           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13))),
% 0.53/0.72      inference('demod', [status(thm)], ['8', '9'])).
% 0.53/0.72  thf('118', plain,
% 0.53/0.72      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.53/0.72         (((X23) = (k1_xboole_0))
% 0.53/0.72          | ((X24) = (k1_xboole_0))
% 0.53/0.72          | ((X25) = (k1_xboole_0))
% 0.53/0.72          | ((k9_mcart_1 @ X23 @ X24 @ X25 @ X27 @ X26)
% 0.53/0.72              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X26))))
% 0.53/0.72          | ~ (m1_subset_1 @ X26 @ 
% 0.53/0.72               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25 @ X27))
% 0.53/0.72          | ((X27) = (k1_xboole_0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['116', '117'])).
% 0.53/0.72  thf('119', plain,
% 0.53/0.72      ((((sk_D) = (k1_xboole_0))
% 0.53/0.72        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.72            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.53/0.72        | ((sk_C) = (k1_xboole_0))
% 0.53/0.72        | ((sk_B) = (k1_xboole_0))
% 0.53/0.72        | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['115', '118'])).
% 0.53/0.72  thf('120', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('121', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('122', plain, (((sk_C) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('123', plain, (((sk_D) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('124', plain,
% 0.53/0.72      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.72         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['119', '120', '121', '122', '123'])).
% 0.53/0.72  thf('125', plain,
% 0.53/0.72      ((((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) != (sk_E))
% 0.53/0.72        | ((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) = (sk_E)))),
% 0.53/0.72      inference('demod', [status(thm)], ['114', '124'])).
% 0.53/0.72  thf('126', plain,
% 0.53/0.72      (((sk_E) != (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('127', plain,
% 0.53/0.72      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.72         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['119', '120', '121', '122', '123'])).
% 0.53/0.72  thf('128', plain,
% 0.53/0.72      (((sk_E) != (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.53/0.72      inference('demod', [status(thm)], ['126', '127'])).
% 0.53/0.72  thf('129', plain,
% 0.53/0.72      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) != (sk_E))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)], ['125', '128'])).
% 0.53/0.72  thf('130', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((X0) != (sk_E))
% 0.53/0.72          | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['112', '129'])).
% 0.53/0.72  thf('131', plain,
% 0.53/0.72      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.72         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)],
% 0.53/0.72                ['119', '120', '121', '122', '123'])).
% 0.53/0.72  thf('132', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((X0) != (sk_E))
% 0.53/0.72          | ((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) = (sk_E)))),
% 0.53/0.72      inference('demod', [status(thm)], ['130', '131'])).
% 0.53/0.72  thf('133', plain,
% 0.53/0.72      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) = (sk_E))),
% 0.53/0.72      inference('simplify', [status(thm)], ['132'])).
% 0.53/0.72  thf('134', plain,
% 0.53/0.72      (((sk_E) != (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.53/0.72      inference('demod', [status(thm)], ['126', '127'])).
% 0.53/0.72  thf('135', plain, ($false),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)], ['133', '134'])).
% 0.53/0.72  
% 0.53/0.72  % SZS output end Refutation
% 0.53/0.72  
% 0.53/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
