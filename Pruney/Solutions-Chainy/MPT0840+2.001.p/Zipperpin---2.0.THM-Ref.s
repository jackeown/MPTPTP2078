%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9c2xiKcGwP

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:21 EST 2020

% Result     : Theorem 13.70s
% Output     : Refutation 13.70s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 265 expanded)
%              Number of leaves         :   26 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          : 1436 (5566 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_2_type,type,(
    sk_F_2: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t51_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
                     => ! [F: $i,G: $i] :
                          ( ( r2_hidden @ ( k4_tarski @ F @ G ) @ ( k4_relset_1 @ A @ B @ B @ C @ D @ E ) )
                        <=> ? [H: $i] :
                              ( ( r2_hidden @ ( k4_tarski @ H @ G ) @ E )
                              & ( r2_hidden @ ( k4_tarski @ F @ H ) @ D )
                              & ( m1_subset_1 @ H @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ~ ( v1_xboole_0 @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
                       => ! [F: $i,G: $i] :
                            ( ( r2_hidden @ ( k4_tarski @ F @ G ) @ ( k4_relset_1 @ A @ B @ B @ C @ D @ E ) )
                          <=> ? [H: $i] :
                                ( ( r2_hidden @ ( k4_tarski @ H @ G ) @ E )
                                & ( r2_hidden @ ( k4_tarski @ F @ H ) @ D )
                                & ( m1_subset_1 @ H @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_relset_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_H @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_H @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('5',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k4_relset_1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D_1 @ X0 )
        = ( k5_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 )
    = ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( X12
       != ( k5_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X16 @ X13 @ X10 @ X11 ) @ X16 ) @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X16 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X16 ) @ ( k5_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X16 @ X13 @ X10 @ X11 ) @ X16 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( ~ ( v1_relat_1 @ sk_E_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_G ) @ sk_E_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_G ) @ sk_E_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['15','18','21'])).

thf('23',plain,
    ( ( ~ ( v1_relat_1 @ sk_E_1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_G ) @ sk_E_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['4','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('25',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_G ) @ sk_E_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( X12
       != ( k5_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_F_1 @ X16 @ X13 @ X10 @ X11 ) ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X16 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X16 ) @ ( k5_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_F_1 @ X16 @ X13 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ~ ( v1_relat_1 @ sk_E_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('34',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ~ ( v1_relat_1 @ sk_E_1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_G ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_B ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_B )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('44',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('49',plain,
    ( ( r2_hidden @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('51',plain,
    ( ( m1_subset_1 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
    | ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_H @ sk_B )
   <= ( m1_subset_1 @ sk_H @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('54',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('55',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['39'])).

thf('57',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ sk_H @ sk_B ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( m1_subset_1 @ sk_H @ sk_B )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 )
    | ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 ) )
    | ~ ( m1_subset_1 @ sk_H @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
    | ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X29 ) @ sk_D_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_G ) @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['39'])).

thf('61',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('62',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('65',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( X12
       != ( k5_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X14 ) @ X10 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('66',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X14 ) @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ ( k5_relat_1 @ X11 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ sk_E_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_G ) @ ( k5_relat_1 @ X0 @ sk_E_1 ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ sk_H ) @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('71',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_G ) @ ( k5_relat_1 @ X0 @ sk_E_1 ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ sk_H ) @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('74',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 )
    = ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('76',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['39'])).

thf('77',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','52','59','60','61','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9c2xiKcGwP
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:33:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 13.70/13.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.70/13.89  % Solved by: fo/fo7.sh
% 13.70/13.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.70/13.89  % done 2357 iterations in 13.426s
% 13.70/13.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.70/13.89  % SZS output start Refutation
% 13.70/13.89  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 13.70/13.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 13.70/13.89  thf(sk_B_type, type, sk_B: $i).
% 13.70/13.89  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 13.70/13.89  thf(sk_H_type, type, sk_H: $i).
% 13.70/13.89  thf(sk_D_1_type, type, sk_D_1: $i).
% 13.70/13.89  thf(sk_G_type, type, sk_G: $i).
% 13.70/13.89  thf(sk_A_type, type, sk_A: $i).
% 13.70/13.89  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 13.70/13.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.70/13.89  thf(sk_F_2_type, type, sk_F_2: $i).
% 13.70/13.89  thf(sk_E_1_type, type, sk_E_1: $i).
% 13.70/13.89  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 13.70/13.89  thf(sk_C_type, type, sk_C: $i).
% 13.70/13.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.70/13.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.70/13.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 13.70/13.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 13.70/13.89  thf(t51_relset_1, conjecture,
% 13.70/13.89    (![A:$i]:
% 13.70/13.89     ( ( ~( v1_xboole_0 @ A ) ) =>
% 13.70/13.89       ( ![B:$i]:
% 13.70/13.89         ( ( ~( v1_xboole_0 @ B ) ) =>
% 13.70/13.89           ( ![C:$i]:
% 13.70/13.89             ( ( ~( v1_xboole_0 @ C ) ) =>
% 13.70/13.89               ( ![D:$i]:
% 13.70/13.89                 ( ( m1_subset_1 @
% 13.70/13.89                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.70/13.89                   ( ![E:$i]:
% 13.70/13.89                     ( ( m1_subset_1 @
% 13.70/13.89                         E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 13.70/13.89                       ( ![F:$i,G:$i]:
% 13.70/13.89                         ( ( r2_hidden @
% 13.70/13.89                             ( k4_tarski @ F @ G ) @ 
% 13.70/13.89                             ( k4_relset_1 @ A @ B @ B @ C @ D @ E ) ) <=>
% 13.70/13.89                           ( ?[H:$i]:
% 13.70/13.89                             ( ( r2_hidden @ ( k4_tarski @ H @ G ) @ E ) & 
% 13.70/13.89                               ( r2_hidden @ ( k4_tarski @ F @ H ) @ D ) & 
% 13.70/13.89                               ( m1_subset_1 @ H @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 13.70/13.89  thf(zf_stmt_0, negated_conjecture,
% 13.70/13.89    (~( ![A:$i]:
% 13.70/13.89        ( ( ~( v1_xboole_0 @ A ) ) =>
% 13.70/13.89          ( ![B:$i]:
% 13.70/13.89            ( ( ~( v1_xboole_0 @ B ) ) =>
% 13.70/13.89              ( ![C:$i]:
% 13.70/13.89                ( ( ~( v1_xboole_0 @ C ) ) =>
% 13.70/13.89                  ( ![D:$i]:
% 13.70/13.89                    ( ( m1_subset_1 @
% 13.70/13.89                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.70/13.89                      ( ![E:$i]:
% 13.70/13.89                        ( ( m1_subset_1 @
% 13.70/13.89                            E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 13.70/13.89                          ( ![F:$i,G:$i]:
% 13.70/13.89                            ( ( r2_hidden @
% 13.70/13.89                                ( k4_tarski @ F @ G ) @ 
% 13.70/13.89                                ( k4_relset_1 @ A @ B @ B @ C @ D @ E ) ) <=>
% 13.70/13.89                              ( ?[H:$i]:
% 13.70/13.89                                ( ( r2_hidden @ ( k4_tarski @ H @ G ) @ E ) & 
% 13.70/13.89                                  ( r2_hidden @ ( k4_tarski @ F @ H ) @ D ) & 
% 13.70/13.89                                  ( m1_subset_1 @ H @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 13.70/13.89    inference('cnf.neg', [status(esa)], [t51_relset_1])).
% 13.70/13.89  thf('0', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)
% 13.70/13.89        | (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 13.70/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.70/13.89  thf('1', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)) | 
% 13.70/13.89       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 13.70/13.89      inference('split', [status(esa)], ['0'])).
% 13.70/13.89  thf('2', plain,
% 13.70/13.89      (((m1_subset_1 @ sk_H @ sk_B)
% 13.70/13.89        | (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 13.70/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.70/13.89  thf('3', plain,
% 13.70/13.89      (((m1_subset_1 @ sk_H @ sk_B)) | 
% 13.70/13.89       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 13.70/13.89      inference('split', [status(esa)], ['2'])).
% 13.70/13.89  thf(dt_k5_relat_1, axiom,
% 13.70/13.89    (![A:$i,B:$i]:
% 13.70/13.89     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 13.70/13.89       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 13.70/13.89  thf('4', plain,
% 13.70/13.89      (![X18 : $i, X19 : $i]:
% 13.70/13.89         (~ (v1_relat_1 @ X18)
% 13.70/13.89          | ~ (v1_relat_1 @ X19)
% 13.70/13.89          | (v1_relat_1 @ (k5_relat_1 @ X18 @ X19)))),
% 13.70/13.89      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 13.70/13.89  thf('5', plain,
% 13.70/13.89      ((m1_subset_1 @ sk_E_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 13.70/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.70/13.89  thf('6', plain,
% 13.70/13.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.70/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.70/13.89  thf(redefinition_k4_relset_1, axiom,
% 13.70/13.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.70/13.89     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 13.70/13.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 13.70/13.89       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 13.70/13.89  thf('7', plain,
% 13.70/13.89      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 13.70/13.89         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 13.70/13.89          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 13.70/13.89          | ((k4_relset_1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 13.70/13.89              = (k5_relat_1 @ X23 @ X26)))),
% 13.70/13.89      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 13.70/13.89  thf('8', plain,
% 13.70/13.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.70/13.89         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D_1 @ X0)
% 13.70/13.89            = (k5_relat_1 @ sk_D_1 @ X0))
% 13.70/13.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 13.70/13.89      inference('sup-', [status(thm)], ['6', '7'])).
% 13.70/13.89  thf('9', plain,
% 13.70/13.89      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)
% 13.70/13.89         = (k5_relat_1 @ sk_D_1 @ sk_E_1))),
% 13.70/13.89      inference('sup-', [status(thm)], ['5', '8'])).
% 13.70/13.89  thf('10', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)
% 13.70/13.89        | (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 13.70/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.70/13.89  thf('11', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('split', [status(esa)], ['10'])).
% 13.70/13.89  thf('12', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89         (k5_relat_1 @ sk_D_1 @ sk_E_1)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup+', [status(thm)], ['9', '11'])).
% 13.70/13.89  thf(d8_relat_1, axiom,
% 13.70/13.89    (![A:$i]:
% 13.70/13.89     ( ( v1_relat_1 @ A ) =>
% 13.70/13.89       ( ![B:$i]:
% 13.70/13.89         ( ( v1_relat_1 @ B ) =>
% 13.70/13.89           ( ![C:$i]:
% 13.70/13.89             ( ( v1_relat_1 @ C ) =>
% 13.70/13.89               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 13.70/13.89                 ( ![D:$i,E:$i]:
% 13.70/13.89                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 13.70/13.89                     ( ?[F:$i]:
% 13.70/13.89                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 13.70/13.89                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 13.70/13.89  thf('13', plain,
% 13.70/13.89      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X16 : $i]:
% 13.70/13.89         (~ (v1_relat_1 @ X10)
% 13.70/13.89          | ((X12) != (k5_relat_1 @ X11 @ X10))
% 13.70/13.89          | (r2_hidden @ 
% 13.70/13.89             (k4_tarski @ (sk_F_1 @ X16 @ X13 @ X10 @ X11) @ X16) @ X10)
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X13 @ X16) @ X12)
% 13.70/13.89          | ~ (v1_relat_1 @ X12)
% 13.70/13.89          | ~ (v1_relat_1 @ X11))),
% 13.70/13.89      inference('cnf', [status(esa)], [d8_relat_1])).
% 13.70/13.89  thf('14', plain,
% 13.70/13.89      (![X10 : $i, X11 : $i, X13 : $i, X16 : $i]:
% 13.70/13.89         (~ (v1_relat_1 @ X11)
% 13.70/13.89          | ~ (v1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X13 @ X16) @ (k5_relat_1 @ X11 @ X10))
% 13.70/13.89          | (r2_hidden @ 
% 13.70/13.89             (k4_tarski @ (sk_F_1 @ X16 @ X13 @ X10 @ X11) @ X16) @ X10)
% 13.70/13.89          | ~ (v1_relat_1 @ X10))),
% 13.70/13.89      inference('simplify', [status(thm)], ['13'])).
% 13.70/13.89  thf('15', plain,
% 13.70/13.89      (((~ (v1_relat_1 @ sk_E_1)
% 13.70/13.89         | (r2_hidden @ 
% 13.70/13.89            (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_G) @ 
% 13.70/13.89            sk_E_1)
% 13.70/13.89         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1))
% 13.70/13.89         | ~ (v1_relat_1 @ sk_D_1)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup-', [status(thm)], ['12', '14'])).
% 13.70/13.89  thf('16', plain,
% 13.70/13.89      ((m1_subset_1 @ sk_E_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 13.70/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.70/13.89  thf(cc1_relset_1, axiom,
% 13.70/13.89    (![A:$i,B:$i,C:$i]:
% 13.70/13.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.70/13.89       ( v1_relat_1 @ C ) ))).
% 13.70/13.89  thf('17', plain,
% 13.70/13.89      (![X20 : $i, X21 : $i, X22 : $i]:
% 13.70/13.89         ((v1_relat_1 @ X20)
% 13.70/13.89          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 13.70/13.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 13.70/13.89  thf('18', plain, ((v1_relat_1 @ sk_E_1)),
% 13.70/13.89      inference('sup-', [status(thm)], ['16', '17'])).
% 13.70/13.89  thf('19', plain,
% 13.70/13.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.70/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.70/13.89  thf('20', plain,
% 13.70/13.89      (![X20 : $i, X21 : $i, X22 : $i]:
% 13.70/13.89         ((v1_relat_1 @ X20)
% 13.70/13.89          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 13.70/13.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 13.70/13.89  thf('21', plain, ((v1_relat_1 @ sk_D_1)),
% 13.70/13.89      inference('sup-', [status(thm)], ['19', '20'])).
% 13.70/13.89  thf('22', plain,
% 13.70/13.89      ((((r2_hidden @ 
% 13.70/13.89          (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_G) @ 
% 13.70/13.89          sk_E_1)
% 13.70/13.89         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1))))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('demod', [status(thm)], ['15', '18', '21'])).
% 13.70/13.89  thf('23', plain,
% 13.70/13.89      (((~ (v1_relat_1 @ sk_E_1)
% 13.70/13.89         | ~ (v1_relat_1 @ sk_D_1)
% 13.70/13.89         | (r2_hidden @ 
% 13.70/13.89            (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_G) @ 
% 13.70/13.89            sk_E_1)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup-', [status(thm)], ['4', '22'])).
% 13.70/13.89  thf('24', plain, ((v1_relat_1 @ sk_E_1)),
% 13.70/13.89      inference('sup-', [status(thm)], ['16', '17'])).
% 13.70/13.89  thf('25', plain, ((v1_relat_1 @ sk_D_1)),
% 13.70/13.89      inference('sup-', [status(thm)], ['19', '20'])).
% 13.70/13.89  thf('26', plain,
% 13.70/13.89      (((r2_hidden @ 
% 13.70/13.89         (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_G) @ 
% 13.70/13.89         sk_E_1))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('demod', [status(thm)], ['23', '24', '25'])).
% 13.70/13.89  thf('27', plain,
% 13.70/13.89      (![X18 : $i, X19 : $i]:
% 13.70/13.89         (~ (v1_relat_1 @ X18)
% 13.70/13.89          | ~ (v1_relat_1 @ X19)
% 13.70/13.89          | (v1_relat_1 @ (k5_relat_1 @ X18 @ X19)))),
% 13.70/13.89      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 13.70/13.89  thf('28', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89         (k5_relat_1 @ sk_D_1 @ sk_E_1)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup+', [status(thm)], ['9', '11'])).
% 13.70/13.89  thf('29', plain,
% 13.70/13.89      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X16 : $i]:
% 13.70/13.89         (~ (v1_relat_1 @ X10)
% 13.70/13.89          | ((X12) != (k5_relat_1 @ X11 @ X10))
% 13.70/13.89          | (r2_hidden @ 
% 13.70/13.89             (k4_tarski @ X13 @ (sk_F_1 @ X16 @ X13 @ X10 @ X11)) @ X11)
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X13 @ X16) @ X12)
% 13.70/13.89          | ~ (v1_relat_1 @ X12)
% 13.70/13.89          | ~ (v1_relat_1 @ X11))),
% 13.70/13.89      inference('cnf', [status(esa)], [d8_relat_1])).
% 13.70/13.89  thf('30', plain,
% 13.70/13.89      (![X10 : $i, X11 : $i, X13 : $i, X16 : $i]:
% 13.70/13.89         (~ (v1_relat_1 @ X11)
% 13.70/13.89          | ~ (v1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X13 @ X16) @ (k5_relat_1 @ X11 @ X10))
% 13.70/13.89          | (r2_hidden @ 
% 13.70/13.89             (k4_tarski @ X13 @ (sk_F_1 @ X16 @ X13 @ X10 @ X11)) @ X11)
% 13.70/13.89          | ~ (v1_relat_1 @ X10))),
% 13.70/13.89      inference('simplify', [status(thm)], ['29'])).
% 13.70/13.89  thf('31', plain,
% 13.70/13.89      (((~ (v1_relat_1 @ sk_E_1)
% 13.70/13.89         | (r2_hidden @ 
% 13.70/13.89            (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 13.70/13.89            sk_D_1)
% 13.70/13.89         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1))
% 13.70/13.89         | ~ (v1_relat_1 @ sk_D_1)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup-', [status(thm)], ['28', '30'])).
% 13.70/13.89  thf('32', plain, ((v1_relat_1 @ sk_E_1)),
% 13.70/13.89      inference('sup-', [status(thm)], ['16', '17'])).
% 13.70/13.89  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 13.70/13.89      inference('sup-', [status(thm)], ['19', '20'])).
% 13.70/13.89  thf('34', plain,
% 13.70/13.89      ((((r2_hidden @ 
% 13.70/13.89          (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 13.70/13.89          sk_D_1)
% 13.70/13.89         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1))))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('demod', [status(thm)], ['31', '32', '33'])).
% 13.70/13.89  thf('35', plain,
% 13.70/13.89      (((~ (v1_relat_1 @ sk_E_1)
% 13.70/13.89         | ~ (v1_relat_1 @ sk_D_1)
% 13.70/13.89         | (r2_hidden @ 
% 13.70/13.89            (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 13.70/13.89            sk_D_1)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup-', [status(thm)], ['27', '34'])).
% 13.70/13.89  thf('36', plain, ((v1_relat_1 @ sk_E_1)),
% 13.70/13.89      inference('sup-', [status(thm)], ['16', '17'])).
% 13.70/13.89  thf('37', plain, ((v1_relat_1 @ sk_D_1)),
% 13.70/13.89      inference('sup-', [status(thm)], ['19', '20'])).
% 13.70/13.89  thf('38', plain,
% 13.70/13.89      (((r2_hidden @ 
% 13.70/13.89         (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 13.70/13.89         sk_D_1))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('demod', [status(thm)], ['35', '36', '37'])).
% 13.70/13.89  thf('39', plain,
% 13.70/13.89      (![X29 : $i]:
% 13.70/13.89         (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1)
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 13.70/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.70/13.89  thf('40', plain,
% 13.70/13.89      ((![X29 : $i]:
% 13.70/13.89          (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1)))
% 13.70/13.89         <= ((![X29 : $i]:
% 13.70/13.89                (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1))))),
% 13.70/13.89      inference('split', [status(esa)], ['39'])).
% 13.70/13.89  thf('41', plain,
% 13.70/13.89      (((~ (r2_hidden @ 
% 13.70/13.89            (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_G) @ 
% 13.70/13.89            sk_E_1)
% 13.70/13.89         | ~ (m1_subset_1 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_B)))
% 13.70/13.89         <= ((![X29 : $i]:
% 13.70/13.89                (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1))) & 
% 13.70/13.89             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup-', [status(thm)], ['38', '40'])).
% 13.70/13.89  thf('42', plain,
% 13.70/13.89      ((~ (m1_subset_1 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_B))
% 13.70/13.89         <= ((![X29 : $i]:
% 13.70/13.89                (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1))) & 
% 13.70/13.89             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup-', [status(thm)], ['26', '41'])).
% 13.70/13.89  thf('43', plain,
% 13.70/13.89      (((r2_hidden @ 
% 13.70/13.89         (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 13.70/13.89         sk_D_1))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('demod', [status(thm)], ['35', '36', '37'])).
% 13.70/13.89  thf('44', plain,
% 13.70/13.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.70/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.70/13.89  thf(l3_subset_1, axiom,
% 13.70/13.89    (![A:$i,B:$i]:
% 13.70/13.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 13.70/13.89       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 13.70/13.89  thf('45', plain,
% 13.70/13.89      (![X5 : $i, X6 : $i, X7 : $i]:
% 13.70/13.89         (~ (r2_hidden @ X5 @ X6)
% 13.70/13.89          | (r2_hidden @ X5 @ X7)
% 13.70/13.89          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 13.70/13.89      inference('cnf', [status(esa)], [l3_subset_1])).
% 13.70/13.89  thf('46', plain,
% 13.70/13.89      (![X0 : $i]:
% 13.70/13.89         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 13.70/13.89          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 13.70/13.89      inference('sup-', [status(thm)], ['44', '45'])).
% 13.70/13.89  thf('47', plain,
% 13.70/13.89      (((r2_hidden @ 
% 13.70/13.89         (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 13.70/13.89         (k2_zfmisc_1 @ sk_A @ sk_B)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup-', [status(thm)], ['43', '46'])).
% 13.70/13.89  thf(l54_zfmisc_1, axiom,
% 13.70/13.89    (![A:$i,B:$i,C:$i,D:$i]:
% 13.70/13.89     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 13.70/13.89       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 13.70/13.89  thf('48', plain,
% 13.70/13.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.70/13.89         ((r2_hidden @ X2 @ X3)
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 13.70/13.89      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 13.70/13.89  thf('49', plain,
% 13.70/13.89      (((r2_hidden @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_B))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup-', [status(thm)], ['47', '48'])).
% 13.70/13.89  thf(t1_subset, axiom,
% 13.70/13.89    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 13.70/13.89  thf('50', plain,
% 13.70/13.89      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 13.70/13.89      inference('cnf', [status(esa)], [t1_subset])).
% 13.70/13.89  thf('51', plain,
% 13.70/13.89      (((m1_subset_1 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_B))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup-', [status(thm)], ['49', '50'])).
% 13.70/13.89  thf('52', plain,
% 13.70/13.89      (~
% 13.70/13.89       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))) | 
% 13.70/13.89       ~
% 13.70/13.89       (![X29 : $i]:
% 13.70/13.89          (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1)))),
% 13.70/13.89      inference('demod', [status(thm)], ['42', '51'])).
% 13.70/13.89  thf('53', plain,
% 13.70/13.89      (((m1_subset_1 @ sk_H @ sk_B)) <= (((m1_subset_1 @ sk_H @ sk_B)))),
% 13.70/13.89      inference('split', [status(esa)], ['2'])).
% 13.70/13.89  thf('54', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 13.70/13.89      inference('split', [status(esa)], ['10'])).
% 13.70/13.89  thf('55', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 13.70/13.89      inference('split', [status(esa)], ['0'])).
% 13.70/13.89  thf('56', plain,
% 13.70/13.89      ((![X29 : $i]:
% 13.70/13.89          (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1)))
% 13.70/13.89         <= ((![X29 : $i]:
% 13.70/13.89                (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1))))),
% 13.70/13.89      inference('split', [status(esa)], ['39'])).
% 13.70/13.89  thf('57', plain,
% 13.70/13.89      (((~ (r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)
% 13.70/13.89         | ~ (m1_subset_1 @ sk_H @ sk_B)))
% 13.70/13.89         <= ((![X29 : $i]:
% 13.70/13.89                (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1))) & 
% 13.70/13.89             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 13.70/13.89      inference('sup-', [status(thm)], ['55', '56'])).
% 13.70/13.89  thf('58', plain,
% 13.70/13.89      ((~ (m1_subset_1 @ sk_H @ sk_B))
% 13.70/13.89         <= ((![X29 : $i]:
% 13.70/13.89                (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1))) & 
% 13.70/13.89             ((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) & 
% 13.70/13.89             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 13.70/13.89      inference('sup-', [status(thm)], ['54', '57'])).
% 13.70/13.89  thf('59', plain,
% 13.70/13.89      (~ ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)) | 
% 13.70/13.89       ~
% 13.70/13.89       (![X29 : $i]:
% 13.70/13.89          (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1))) | 
% 13.70/13.89       ~ ((m1_subset_1 @ sk_H @ sk_B)) | 
% 13.70/13.89       ~ ((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1))),
% 13.70/13.89      inference('sup-', [status(thm)], ['53', '58'])).
% 13.70/13.89  thf('60', plain,
% 13.70/13.89      (~
% 13.70/13.89       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))) | 
% 13.70/13.89       (![X29 : $i]:
% 13.70/13.89          (~ (m1_subset_1 @ X29 @ sk_B)
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X29) @ sk_D_1)
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_G) @ sk_E_1)))),
% 13.70/13.89      inference('split', [status(esa)], ['39'])).
% 13.70/13.89  thf('61', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) | 
% 13.70/13.89       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 13.70/13.89      inference('split', [status(esa)], ['10'])).
% 13.70/13.89  thf('62', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 13.70/13.89      inference('split', [status(esa)], ['0'])).
% 13.70/13.89  thf('63', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 13.70/13.89      inference('split', [status(esa)], ['10'])).
% 13.70/13.89  thf('64', plain,
% 13.70/13.89      (![X18 : $i, X19 : $i]:
% 13.70/13.89         (~ (v1_relat_1 @ X18)
% 13.70/13.89          | ~ (v1_relat_1 @ X19)
% 13.70/13.89          | (v1_relat_1 @ (k5_relat_1 @ X18 @ X19)))),
% 13.70/13.89      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 13.70/13.89  thf('65', plain,
% 13.70/13.89      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 13.70/13.89         (~ (v1_relat_1 @ X10)
% 13.70/13.89          | ((X12) != (k5_relat_1 @ X11 @ X10))
% 13.70/13.89          | (r2_hidden @ (k4_tarski @ X13 @ X14) @ X12)
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ X11)
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X15 @ X14) @ X10)
% 13.70/13.89          | ~ (v1_relat_1 @ X12)
% 13.70/13.89          | ~ (v1_relat_1 @ X11))),
% 13.70/13.89      inference('cnf', [status(esa)], [d8_relat_1])).
% 13.70/13.89  thf('66', plain,
% 13.70/13.89      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 13.70/13.89         (~ (v1_relat_1 @ X11)
% 13.70/13.89          | ~ (v1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X15 @ X14) @ X10)
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ X11)
% 13.70/13.89          | (r2_hidden @ (k4_tarski @ X13 @ X14) @ (k5_relat_1 @ X11 @ X10))
% 13.70/13.89          | ~ (v1_relat_1 @ X10))),
% 13.70/13.89      inference('simplify', [status(thm)], ['65'])).
% 13.70/13.89  thf('67', plain,
% 13.70/13.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.70/13.89         (~ (v1_relat_1 @ X0)
% 13.70/13.89          | ~ (v1_relat_1 @ X1)
% 13.70/13.89          | ~ (v1_relat_1 @ X0)
% 13.70/13.89          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 13.70/13.89          | ~ (v1_relat_1 @ X1))),
% 13.70/13.89      inference('sup-', [status(thm)], ['64', '66'])).
% 13.70/13.89  thf('68', plain,
% 13.70/13.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.70/13.89         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 13.70/13.89          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 13.70/13.89          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 13.70/13.89          | ~ (v1_relat_1 @ X1)
% 13.70/13.89          | ~ (v1_relat_1 @ X0))),
% 13.70/13.89      inference('simplify', [status(thm)], ['67'])).
% 13.70/13.89  thf('69', plain,
% 13.70/13.89      ((![X0 : $i, X1 : $i]:
% 13.70/13.89          (~ (v1_relat_1 @ sk_E_1)
% 13.70/13.89           | ~ (v1_relat_1 @ X0)
% 13.70/13.89           | (r2_hidden @ (k4_tarski @ X1 @ sk_G) @ (k5_relat_1 @ X0 @ sk_E_1))
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ X1 @ sk_H) @ X0)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 13.70/13.89      inference('sup-', [status(thm)], ['63', '68'])).
% 13.70/13.89  thf('70', plain, ((v1_relat_1 @ sk_E_1)),
% 13.70/13.89      inference('sup-', [status(thm)], ['16', '17'])).
% 13.70/13.89  thf('71', plain,
% 13.70/13.89      ((![X0 : $i, X1 : $i]:
% 13.70/13.89          (~ (v1_relat_1 @ X0)
% 13.70/13.89           | (r2_hidden @ (k4_tarski @ X1 @ sk_G) @ (k5_relat_1 @ X0 @ sk_E_1))
% 13.70/13.89           | ~ (r2_hidden @ (k4_tarski @ X1 @ sk_H) @ X0)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 13.70/13.89      inference('demod', [status(thm)], ['69', '70'])).
% 13.70/13.89  thf('72', plain,
% 13.70/13.89      ((((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89          (k5_relat_1 @ sk_D_1 @ sk_E_1))
% 13.70/13.89         | ~ (v1_relat_1 @ sk_D_1)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) & 
% 13.70/13.89             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 13.70/13.89      inference('sup-', [status(thm)], ['62', '71'])).
% 13.70/13.89  thf('73', plain, ((v1_relat_1 @ sk_D_1)),
% 13.70/13.89      inference('sup-', [status(thm)], ['19', '20'])).
% 13.70/13.89  thf('74', plain,
% 13.70/13.89      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89         (k5_relat_1 @ sk_D_1 @ sk_E_1)))
% 13.70/13.89         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) & 
% 13.70/13.89             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 13.70/13.89      inference('demod', [status(thm)], ['72', '73'])).
% 13.70/13.89  thf('75', plain,
% 13.70/13.89      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)
% 13.70/13.89         = (k5_relat_1 @ sk_D_1 @ sk_E_1))),
% 13.70/13.89      inference('sup-', [status(thm)], ['5', '8'])).
% 13.70/13.89  thf('76', plain,
% 13.70/13.89      ((~ (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))
% 13.70/13.89         <= (~
% 13.70/13.89             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('split', [status(esa)], ['39'])).
% 13.70/13.89  thf('77', plain,
% 13.70/13.89      ((~ (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89           (k5_relat_1 @ sk_D_1 @ sk_E_1)))
% 13.70/13.89         <= (~
% 13.70/13.89             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 13.70/13.89      inference('sup-', [status(thm)], ['75', '76'])).
% 13.70/13.89  thf('78', plain,
% 13.70/13.89      (~ ((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) | 
% 13.70/13.89       ~ ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)) | 
% 13.70/13.89       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 13.70/13.89         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 13.70/13.89      inference('sup-', [status(thm)], ['74', '77'])).
% 13.70/13.89  thf('79', plain, ($false),
% 13.70/13.89      inference('sat_resolution*', [status(thm)],
% 13.70/13.89                ['1', '3', '52', '59', '60', '61', '78'])).
% 13.70/13.89  
% 13.70/13.89  % SZS output end Refutation
% 13.70/13.89  
% 13.70/13.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
