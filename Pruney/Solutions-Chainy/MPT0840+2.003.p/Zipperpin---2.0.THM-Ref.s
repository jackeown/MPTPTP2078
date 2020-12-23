%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.98ZbXelfvo

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:22 EST 2020

% Result     : Theorem 56.78s
% Output     : Refutation 56.78s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 307 expanded)
%              Number of leaves         :   27 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          : 1460 (5762 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_F_2_type,type,(
    sk_F_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

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
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X20 @ X21 ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( X14
       != ( k5_relat_1 @ X13 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X18 @ X15 @ X12 @ X13 ) @ X18 ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X18 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('14',plain,(
    ! [X12: $i,X13: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X18 ) @ ( k5_relat_1 @ X13 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X18 @ X15 @ X12 @ X13 ) @ X18 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_G ) @ sk_E_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['15','20','25'])).

thf('27',plain,
    ( ( ~ ( v1_relat_1 @ sk_E_1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_G ) @ sk_E_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('29',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_G ) @ sk_E_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( X14
       != ( k5_relat_1 @ X13 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( sk_F_1 @ X18 @ X15 @ X12 @ X13 ) ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X18 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X18 ) @ ( k5_relat_1 @ X13 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( sk_F_1 @ X18 @ X15 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ~ ( v1_relat_1 @ sk_E_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('38',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ~ ( v1_relat_1 @ sk_E_1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_G ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_B ) )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ~ ( m1_subset_1 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_B )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('48',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('53',plain,
    ( ( r2_hidden @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('55',plain,
    ( ( m1_subset_1 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
    | ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['46','55'])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_H @ sk_B )
   <= ( m1_subset_1 @ sk_H @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('58',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('59',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['43'])).

thf('61',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ sk_H @ sk_B ) )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( m1_subset_1 @ sk_H @ sk_B )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 )
    | ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 ) )
    | ~ ( m1_subset_1 @ sk_H @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
    | ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X30 ) @ sk_D_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_G ) @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['43'])).

thf('65',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('66',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('69',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( X14
       != ( k5_relat_1 @ X13 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('70',plain,(
    ! [X12: $i,X13: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ ( k5_relat_1 @ X13 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ sk_E_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_G ) @ ( k5_relat_1 @ X0 @ sk_E_1 ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ sk_H ) @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_G ) @ ( k5_relat_1 @ X0 @ sk_E_1 ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ sk_H ) @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('78',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 )
    = ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('80',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['43'])).

thf('81',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','56','63','64','65','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.98ZbXelfvo
% 0.16/0.37  % Computer   : n017.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 15:08:17 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 56.78/57.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 56.78/57.06  % Solved by: fo/fo7.sh
% 56.78/57.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 56.78/57.06  % done 4010 iterations in 56.579s
% 56.78/57.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 56.78/57.06  % SZS output start Refutation
% 56.78/57.06  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 56.78/57.06  thf(sk_E_1_type, type, sk_E_1: $i).
% 56.78/57.06  thf(sk_F_2_type, type, sk_F_2: $i).
% 56.78/57.06  thf(sk_A_type, type, sk_A: $i).
% 56.78/57.06  thf(sk_D_1_type, type, sk_D_1: $i).
% 56.78/57.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 56.78/57.06  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 56.78/57.06  thf(sk_C_type, type, sk_C: $i).
% 56.78/57.06  thf(sk_B_type, type, sk_B: $i).
% 56.78/57.06  thf(sk_G_type, type, sk_G: $i).
% 56.78/57.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 56.78/57.06  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 56.78/57.06  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 56.78/57.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 56.78/57.06  thf(sk_H_type, type, sk_H: $i).
% 56.78/57.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 56.78/57.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 56.78/57.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 56.78/57.06  thf(t51_relset_1, conjecture,
% 56.78/57.06    (![A:$i]:
% 56.78/57.06     ( ( ~( v1_xboole_0 @ A ) ) =>
% 56.78/57.06       ( ![B:$i]:
% 56.78/57.06         ( ( ~( v1_xboole_0 @ B ) ) =>
% 56.78/57.06           ( ![C:$i]:
% 56.78/57.06             ( ( ~( v1_xboole_0 @ C ) ) =>
% 56.78/57.06               ( ![D:$i]:
% 56.78/57.06                 ( ( m1_subset_1 @
% 56.78/57.06                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 56.78/57.06                   ( ![E:$i]:
% 56.78/57.06                     ( ( m1_subset_1 @
% 56.78/57.06                         E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 56.78/57.06                       ( ![F:$i,G:$i]:
% 56.78/57.06                         ( ( r2_hidden @
% 56.78/57.06                             ( k4_tarski @ F @ G ) @ 
% 56.78/57.06                             ( k4_relset_1 @ A @ B @ B @ C @ D @ E ) ) <=>
% 56.78/57.06                           ( ?[H:$i]:
% 56.78/57.06                             ( ( r2_hidden @ ( k4_tarski @ H @ G ) @ E ) & 
% 56.78/57.06                               ( r2_hidden @ ( k4_tarski @ F @ H ) @ D ) & 
% 56.78/57.06                               ( m1_subset_1 @ H @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 56.78/57.06  thf(zf_stmt_0, negated_conjecture,
% 56.78/57.06    (~( ![A:$i]:
% 56.78/57.06        ( ( ~( v1_xboole_0 @ A ) ) =>
% 56.78/57.06          ( ![B:$i]:
% 56.78/57.06            ( ( ~( v1_xboole_0 @ B ) ) =>
% 56.78/57.06              ( ![C:$i]:
% 56.78/57.06                ( ( ~( v1_xboole_0 @ C ) ) =>
% 56.78/57.06                  ( ![D:$i]:
% 56.78/57.06                    ( ( m1_subset_1 @
% 56.78/57.06                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 56.78/57.06                      ( ![E:$i]:
% 56.78/57.06                        ( ( m1_subset_1 @
% 56.78/57.06                            E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 56.78/57.06                          ( ![F:$i,G:$i]:
% 56.78/57.06                            ( ( r2_hidden @
% 56.78/57.06                                ( k4_tarski @ F @ G ) @ 
% 56.78/57.06                                ( k4_relset_1 @ A @ B @ B @ C @ D @ E ) ) <=>
% 56.78/57.06                              ( ?[H:$i]:
% 56.78/57.06                                ( ( r2_hidden @ ( k4_tarski @ H @ G ) @ E ) & 
% 56.78/57.06                                  ( r2_hidden @ ( k4_tarski @ F @ H ) @ D ) & 
% 56.78/57.06                                  ( m1_subset_1 @ H @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 56.78/57.06    inference('cnf.neg', [status(esa)], [t51_relset_1])).
% 56.78/57.06  thf('0', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)
% 56.78/57.06        | (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 56.78/57.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.78/57.06  thf('1', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)) | 
% 56.78/57.06       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 56.78/57.06      inference('split', [status(esa)], ['0'])).
% 56.78/57.06  thf('2', plain,
% 56.78/57.06      (((m1_subset_1 @ sk_H @ sk_B)
% 56.78/57.06        | (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 56.78/57.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.78/57.06  thf('3', plain,
% 56.78/57.06      (((m1_subset_1 @ sk_H @ sk_B)) | 
% 56.78/57.06       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 56.78/57.06      inference('split', [status(esa)], ['2'])).
% 56.78/57.06  thf(dt_k5_relat_1, axiom,
% 56.78/57.06    (![A:$i,B:$i]:
% 56.78/57.06     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 56.78/57.06       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 56.78/57.06  thf('4', plain,
% 56.78/57.06      (![X20 : $i, X21 : $i]:
% 56.78/57.06         (~ (v1_relat_1 @ X20)
% 56.78/57.06          | ~ (v1_relat_1 @ X21)
% 56.78/57.06          | (v1_relat_1 @ (k5_relat_1 @ X20 @ X21)))),
% 56.78/57.06      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 56.78/57.06  thf('5', plain,
% 56.78/57.06      ((m1_subset_1 @ sk_E_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 56.78/57.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.78/57.06  thf('6', plain,
% 56.78/57.06      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 56.78/57.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.78/57.06  thf(redefinition_k4_relset_1, axiom,
% 56.78/57.06    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 56.78/57.06     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 56.78/57.06         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 56.78/57.06       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 56.78/57.06  thf('7', plain,
% 56.78/57.06      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 56.78/57.06         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 56.78/57.06          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 56.78/57.06          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 56.78/57.06              = (k5_relat_1 @ X24 @ X27)))),
% 56.78/57.06      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 56.78/57.06  thf('8', plain,
% 56.78/57.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.78/57.06         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D_1 @ X0)
% 56.78/57.06            = (k5_relat_1 @ sk_D_1 @ X0))
% 56.78/57.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 56.78/57.06      inference('sup-', [status(thm)], ['6', '7'])).
% 56.78/57.06  thf('9', plain,
% 56.78/57.06      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)
% 56.78/57.06         = (k5_relat_1 @ sk_D_1 @ sk_E_1))),
% 56.78/57.06      inference('sup-', [status(thm)], ['5', '8'])).
% 56.78/57.06  thf('10', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)
% 56.78/57.06        | (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 56.78/57.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.78/57.06  thf('11', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('split', [status(esa)], ['10'])).
% 56.78/57.06  thf('12', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06         (k5_relat_1 @ sk_D_1 @ sk_E_1)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup+', [status(thm)], ['9', '11'])).
% 56.78/57.06  thf(d8_relat_1, axiom,
% 56.78/57.06    (![A:$i]:
% 56.78/57.06     ( ( v1_relat_1 @ A ) =>
% 56.78/57.06       ( ![B:$i]:
% 56.78/57.06         ( ( v1_relat_1 @ B ) =>
% 56.78/57.06           ( ![C:$i]:
% 56.78/57.06             ( ( v1_relat_1 @ C ) =>
% 56.78/57.06               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 56.78/57.06                 ( ![D:$i,E:$i]:
% 56.78/57.06                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 56.78/57.06                     ( ?[F:$i]:
% 56.78/57.06                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 56.78/57.06                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 56.78/57.06  thf('13', plain,
% 56.78/57.06      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X18 : $i]:
% 56.78/57.06         (~ (v1_relat_1 @ X12)
% 56.78/57.06          | ((X14) != (k5_relat_1 @ X13 @ X12))
% 56.78/57.06          | (r2_hidden @ 
% 56.78/57.06             (k4_tarski @ (sk_F_1 @ X18 @ X15 @ X12 @ X13) @ X18) @ X12)
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X15 @ X18) @ X14)
% 56.78/57.06          | ~ (v1_relat_1 @ X14)
% 56.78/57.06          | ~ (v1_relat_1 @ X13))),
% 56.78/57.06      inference('cnf', [status(esa)], [d8_relat_1])).
% 56.78/57.06  thf('14', plain,
% 56.78/57.06      (![X12 : $i, X13 : $i, X15 : $i, X18 : $i]:
% 56.78/57.06         (~ (v1_relat_1 @ X13)
% 56.78/57.06          | ~ (v1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X15 @ X18) @ (k5_relat_1 @ X13 @ X12))
% 56.78/57.06          | (r2_hidden @ 
% 56.78/57.06             (k4_tarski @ (sk_F_1 @ X18 @ X15 @ X12 @ X13) @ X18) @ X12)
% 56.78/57.06          | ~ (v1_relat_1 @ X12))),
% 56.78/57.06      inference('simplify', [status(thm)], ['13'])).
% 56.78/57.06  thf('15', plain,
% 56.78/57.06      (((~ (v1_relat_1 @ sk_E_1)
% 56.78/57.06         | (r2_hidden @ 
% 56.78/57.06            (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_G) @ 
% 56.78/57.06            sk_E_1)
% 56.78/57.06         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1))
% 56.78/57.06         | ~ (v1_relat_1 @ sk_D_1)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup-', [status(thm)], ['12', '14'])).
% 56.78/57.06  thf('16', plain,
% 56.78/57.06      ((m1_subset_1 @ sk_E_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 56.78/57.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.78/57.06  thf(cc2_relat_1, axiom,
% 56.78/57.06    (![A:$i]:
% 56.78/57.06     ( ( v1_relat_1 @ A ) =>
% 56.78/57.06       ( ![B:$i]:
% 56.78/57.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 56.78/57.06  thf('17', plain,
% 56.78/57.06      (![X10 : $i, X11 : $i]:
% 56.78/57.06         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 56.78/57.06          | (v1_relat_1 @ X10)
% 56.78/57.06          | ~ (v1_relat_1 @ X11))),
% 56.78/57.06      inference('cnf', [status(esa)], [cc2_relat_1])).
% 56.78/57.06  thf('18', plain,
% 56.78/57.06      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E_1))),
% 56.78/57.06      inference('sup-', [status(thm)], ['16', '17'])).
% 56.78/57.06  thf(fc6_relat_1, axiom,
% 56.78/57.06    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 56.78/57.06  thf('19', plain,
% 56.78/57.06      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 56.78/57.06      inference('cnf', [status(esa)], [fc6_relat_1])).
% 56.78/57.06  thf('20', plain, ((v1_relat_1 @ sk_E_1)),
% 56.78/57.06      inference('demod', [status(thm)], ['18', '19'])).
% 56.78/57.06  thf('21', plain,
% 56.78/57.06      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 56.78/57.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.78/57.06  thf('22', plain,
% 56.78/57.06      (![X10 : $i, X11 : $i]:
% 56.78/57.06         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 56.78/57.06          | (v1_relat_1 @ X10)
% 56.78/57.06          | ~ (v1_relat_1 @ X11))),
% 56.78/57.06      inference('cnf', [status(esa)], [cc2_relat_1])).
% 56.78/57.06  thf('23', plain,
% 56.78/57.06      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 56.78/57.06      inference('sup-', [status(thm)], ['21', '22'])).
% 56.78/57.06  thf('24', plain,
% 56.78/57.06      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 56.78/57.06      inference('cnf', [status(esa)], [fc6_relat_1])).
% 56.78/57.06  thf('25', plain, ((v1_relat_1 @ sk_D_1)),
% 56.78/57.06      inference('demod', [status(thm)], ['23', '24'])).
% 56.78/57.06  thf('26', plain,
% 56.78/57.06      ((((r2_hidden @ 
% 56.78/57.06          (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_G) @ 
% 56.78/57.06          sk_E_1)
% 56.78/57.06         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1))))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('demod', [status(thm)], ['15', '20', '25'])).
% 56.78/57.06  thf('27', plain,
% 56.78/57.06      (((~ (v1_relat_1 @ sk_E_1)
% 56.78/57.06         | ~ (v1_relat_1 @ sk_D_1)
% 56.78/57.06         | (r2_hidden @ 
% 56.78/57.06            (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_G) @ 
% 56.78/57.06            sk_E_1)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup-', [status(thm)], ['4', '26'])).
% 56.78/57.06  thf('28', plain, ((v1_relat_1 @ sk_E_1)),
% 56.78/57.06      inference('demod', [status(thm)], ['18', '19'])).
% 56.78/57.06  thf('29', plain, ((v1_relat_1 @ sk_D_1)),
% 56.78/57.06      inference('demod', [status(thm)], ['23', '24'])).
% 56.78/57.06  thf('30', plain,
% 56.78/57.06      (((r2_hidden @ 
% 56.78/57.06         (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_G) @ 
% 56.78/57.06         sk_E_1))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('demod', [status(thm)], ['27', '28', '29'])).
% 56.78/57.06  thf('31', plain,
% 56.78/57.06      (![X20 : $i, X21 : $i]:
% 56.78/57.06         (~ (v1_relat_1 @ X20)
% 56.78/57.06          | ~ (v1_relat_1 @ X21)
% 56.78/57.06          | (v1_relat_1 @ (k5_relat_1 @ X20 @ X21)))),
% 56.78/57.06      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 56.78/57.06  thf('32', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06         (k5_relat_1 @ sk_D_1 @ sk_E_1)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup+', [status(thm)], ['9', '11'])).
% 56.78/57.06  thf('33', plain,
% 56.78/57.06      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X18 : $i]:
% 56.78/57.06         (~ (v1_relat_1 @ X12)
% 56.78/57.06          | ((X14) != (k5_relat_1 @ X13 @ X12))
% 56.78/57.06          | (r2_hidden @ 
% 56.78/57.06             (k4_tarski @ X15 @ (sk_F_1 @ X18 @ X15 @ X12 @ X13)) @ X13)
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X15 @ X18) @ X14)
% 56.78/57.06          | ~ (v1_relat_1 @ X14)
% 56.78/57.06          | ~ (v1_relat_1 @ X13))),
% 56.78/57.06      inference('cnf', [status(esa)], [d8_relat_1])).
% 56.78/57.06  thf('34', plain,
% 56.78/57.06      (![X12 : $i, X13 : $i, X15 : $i, X18 : $i]:
% 56.78/57.06         (~ (v1_relat_1 @ X13)
% 56.78/57.06          | ~ (v1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X15 @ X18) @ (k5_relat_1 @ X13 @ X12))
% 56.78/57.06          | (r2_hidden @ 
% 56.78/57.06             (k4_tarski @ X15 @ (sk_F_1 @ X18 @ X15 @ X12 @ X13)) @ X13)
% 56.78/57.06          | ~ (v1_relat_1 @ X12))),
% 56.78/57.06      inference('simplify', [status(thm)], ['33'])).
% 56.78/57.06  thf('35', plain,
% 56.78/57.06      (((~ (v1_relat_1 @ sk_E_1)
% 56.78/57.06         | (r2_hidden @ 
% 56.78/57.06            (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 56.78/57.06            sk_D_1)
% 56.78/57.06         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1))
% 56.78/57.06         | ~ (v1_relat_1 @ sk_D_1)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup-', [status(thm)], ['32', '34'])).
% 56.78/57.06  thf('36', plain, ((v1_relat_1 @ sk_E_1)),
% 56.78/57.06      inference('demod', [status(thm)], ['18', '19'])).
% 56.78/57.06  thf('37', plain, ((v1_relat_1 @ sk_D_1)),
% 56.78/57.06      inference('demod', [status(thm)], ['23', '24'])).
% 56.78/57.06  thf('38', plain,
% 56.78/57.06      ((((r2_hidden @ 
% 56.78/57.06          (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 56.78/57.06          sk_D_1)
% 56.78/57.06         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1))))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('demod', [status(thm)], ['35', '36', '37'])).
% 56.78/57.06  thf('39', plain,
% 56.78/57.06      (((~ (v1_relat_1 @ sk_E_1)
% 56.78/57.06         | ~ (v1_relat_1 @ sk_D_1)
% 56.78/57.06         | (r2_hidden @ 
% 56.78/57.06            (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 56.78/57.06            sk_D_1)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup-', [status(thm)], ['31', '38'])).
% 56.78/57.06  thf('40', plain, ((v1_relat_1 @ sk_E_1)),
% 56.78/57.06      inference('demod', [status(thm)], ['18', '19'])).
% 56.78/57.06  thf('41', plain, ((v1_relat_1 @ sk_D_1)),
% 56.78/57.06      inference('demod', [status(thm)], ['23', '24'])).
% 56.78/57.06  thf('42', plain,
% 56.78/57.06      (((r2_hidden @ 
% 56.78/57.06         (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 56.78/57.06         sk_D_1))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('demod', [status(thm)], ['39', '40', '41'])).
% 56.78/57.06  thf('43', plain,
% 56.78/57.06      (![X30 : $i]:
% 56.78/57.06         (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1)
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 56.78/57.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.78/57.06  thf('44', plain,
% 56.78/57.06      ((![X30 : $i]:
% 56.78/57.06          (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1)))
% 56.78/57.06         <= ((![X30 : $i]:
% 56.78/57.06                (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1))))),
% 56.78/57.06      inference('split', [status(esa)], ['43'])).
% 56.78/57.06  thf('45', plain,
% 56.78/57.06      (((~ (r2_hidden @ 
% 56.78/57.06            (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_G) @ 
% 56.78/57.06            sk_E_1)
% 56.78/57.06         | ~ (m1_subset_1 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_B)))
% 56.78/57.06         <= ((![X30 : $i]:
% 56.78/57.06                (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1))) & 
% 56.78/57.06             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup-', [status(thm)], ['42', '44'])).
% 56.78/57.06  thf('46', plain,
% 56.78/57.06      ((~ (m1_subset_1 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_B))
% 56.78/57.06         <= ((![X30 : $i]:
% 56.78/57.06                (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1))) & 
% 56.78/57.06             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup-', [status(thm)], ['30', '45'])).
% 56.78/57.06  thf('47', plain,
% 56.78/57.06      (((r2_hidden @ 
% 56.78/57.06         (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 56.78/57.06         sk_D_1))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('demod', [status(thm)], ['39', '40', '41'])).
% 56.78/57.06  thf('48', plain,
% 56.78/57.06      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 56.78/57.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.78/57.06  thf(l3_subset_1, axiom,
% 56.78/57.06    (![A:$i,B:$i]:
% 56.78/57.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 56.78/57.06       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 56.78/57.06  thf('49', plain,
% 56.78/57.06      (![X5 : $i, X6 : $i, X7 : $i]:
% 56.78/57.06         (~ (r2_hidden @ X5 @ X6)
% 56.78/57.06          | (r2_hidden @ X5 @ X7)
% 56.78/57.06          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 56.78/57.06      inference('cnf', [status(esa)], [l3_subset_1])).
% 56.78/57.06  thf('50', plain,
% 56.78/57.06      (![X0 : $i]:
% 56.78/57.06         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 56.78/57.06          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 56.78/57.06      inference('sup-', [status(thm)], ['48', '49'])).
% 56.78/57.06  thf('51', plain,
% 56.78/57.06      (((r2_hidden @ 
% 56.78/57.06         (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1)) @ 
% 56.78/57.06         (k2_zfmisc_1 @ sk_A @ sk_B)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup-', [status(thm)], ['47', '50'])).
% 56.78/57.06  thf(l54_zfmisc_1, axiom,
% 56.78/57.06    (![A:$i,B:$i,C:$i,D:$i]:
% 56.78/57.06     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 56.78/57.06       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 56.78/57.06  thf('52', plain,
% 56.78/57.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.78/57.06         ((r2_hidden @ X2 @ X3)
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 56.78/57.06      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 56.78/57.06  thf('53', plain,
% 56.78/57.06      (((r2_hidden @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_B))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup-', [status(thm)], ['51', '52'])).
% 56.78/57.06  thf(t1_subset, axiom,
% 56.78/57.06    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 56.78/57.06  thf('54', plain,
% 56.78/57.06      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 56.78/57.06      inference('cnf', [status(esa)], [t1_subset])).
% 56.78/57.06  thf('55', plain,
% 56.78/57.06      (((m1_subset_1 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_1) @ sk_B))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup-', [status(thm)], ['53', '54'])).
% 56.78/57.06  thf('56', plain,
% 56.78/57.06      (~
% 56.78/57.06       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))) | 
% 56.78/57.06       ~
% 56.78/57.06       (![X30 : $i]:
% 56.78/57.06          (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1)))),
% 56.78/57.06      inference('demod', [status(thm)], ['46', '55'])).
% 56.78/57.06  thf('57', plain,
% 56.78/57.06      (((m1_subset_1 @ sk_H @ sk_B)) <= (((m1_subset_1 @ sk_H @ sk_B)))),
% 56.78/57.06      inference('split', [status(esa)], ['2'])).
% 56.78/57.06  thf('58', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 56.78/57.06      inference('split', [status(esa)], ['10'])).
% 56.78/57.06  thf('59', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 56.78/57.06      inference('split', [status(esa)], ['0'])).
% 56.78/57.06  thf('60', plain,
% 56.78/57.06      ((![X30 : $i]:
% 56.78/57.06          (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1)))
% 56.78/57.06         <= ((![X30 : $i]:
% 56.78/57.06                (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1))))),
% 56.78/57.06      inference('split', [status(esa)], ['43'])).
% 56.78/57.06  thf('61', plain,
% 56.78/57.06      (((~ (r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)
% 56.78/57.06         | ~ (m1_subset_1 @ sk_H @ sk_B)))
% 56.78/57.06         <= ((![X30 : $i]:
% 56.78/57.06                (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1))) & 
% 56.78/57.06             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 56.78/57.06      inference('sup-', [status(thm)], ['59', '60'])).
% 56.78/57.06  thf('62', plain,
% 56.78/57.06      ((~ (m1_subset_1 @ sk_H @ sk_B))
% 56.78/57.06         <= ((![X30 : $i]:
% 56.78/57.06                (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06                 | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1))) & 
% 56.78/57.06             ((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) & 
% 56.78/57.06             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 56.78/57.06      inference('sup-', [status(thm)], ['58', '61'])).
% 56.78/57.06  thf('63', plain,
% 56.78/57.06      (~ ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)) | 
% 56.78/57.06       ~
% 56.78/57.06       (![X30 : $i]:
% 56.78/57.06          (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1))) | 
% 56.78/57.06       ~ ((m1_subset_1 @ sk_H @ sk_B)) | 
% 56.78/57.06       ~ ((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1))),
% 56.78/57.06      inference('sup-', [status(thm)], ['57', '62'])).
% 56.78/57.06  thf('64', plain,
% 56.78/57.06      (~
% 56.78/57.06       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))) | 
% 56.78/57.06       (![X30 : $i]:
% 56.78/57.06          (~ (m1_subset_1 @ X30 @ sk_B)
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X30) @ sk_D_1)
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_G) @ sk_E_1)))),
% 56.78/57.06      inference('split', [status(esa)], ['43'])).
% 56.78/57.06  thf('65', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) | 
% 56.78/57.06       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 56.78/57.06      inference('split', [status(esa)], ['10'])).
% 56.78/57.06  thf('66', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 56.78/57.06      inference('split', [status(esa)], ['0'])).
% 56.78/57.06  thf('67', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 56.78/57.06      inference('split', [status(esa)], ['10'])).
% 56.78/57.06  thf('68', plain,
% 56.78/57.06      (![X20 : $i, X21 : $i]:
% 56.78/57.06         (~ (v1_relat_1 @ X20)
% 56.78/57.06          | ~ (v1_relat_1 @ X21)
% 56.78/57.06          | (v1_relat_1 @ (k5_relat_1 @ X20 @ X21)))),
% 56.78/57.06      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 56.78/57.06  thf('69', plain,
% 56.78/57.06      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 56.78/57.06         (~ (v1_relat_1 @ X12)
% 56.78/57.06          | ((X14) != (k5_relat_1 @ X13 @ X12))
% 56.78/57.06          | (r2_hidden @ (k4_tarski @ X15 @ X16) @ X14)
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X13)
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X17 @ X16) @ X12)
% 56.78/57.06          | ~ (v1_relat_1 @ X14)
% 56.78/57.06          | ~ (v1_relat_1 @ X13))),
% 56.78/57.06      inference('cnf', [status(esa)], [d8_relat_1])).
% 56.78/57.06  thf('70', plain,
% 56.78/57.06      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 56.78/57.06         (~ (v1_relat_1 @ X13)
% 56.78/57.06          | ~ (v1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X17 @ X16) @ X12)
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X13)
% 56.78/57.06          | (r2_hidden @ (k4_tarski @ X15 @ X16) @ (k5_relat_1 @ X13 @ X12))
% 56.78/57.06          | ~ (v1_relat_1 @ X12))),
% 56.78/57.06      inference('simplify', [status(thm)], ['69'])).
% 56.78/57.06  thf('71', plain,
% 56.78/57.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 56.78/57.06         (~ (v1_relat_1 @ X0)
% 56.78/57.06          | ~ (v1_relat_1 @ X1)
% 56.78/57.06          | ~ (v1_relat_1 @ X0)
% 56.78/57.06          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 56.78/57.06          | ~ (v1_relat_1 @ X1))),
% 56.78/57.06      inference('sup-', [status(thm)], ['68', '70'])).
% 56.78/57.06  thf('72', plain,
% 56.78/57.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 56.78/57.06         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 56.78/57.06          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 56.78/57.06          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 56.78/57.06          | ~ (v1_relat_1 @ X1)
% 56.78/57.06          | ~ (v1_relat_1 @ X0))),
% 56.78/57.06      inference('simplify', [status(thm)], ['71'])).
% 56.78/57.06  thf('73', plain,
% 56.78/57.06      ((![X0 : $i, X1 : $i]:
% 56.78/57.06          (~ (v1_relat_1 @ sk_E_1)
% 56.78/57.06           | ~ (v1_relat_1 @ X0)
% 56.78/57.06           | (r2_hidden @ (k4_tarski @ X1 @ sk_G) @ (k5_relat_1 @ X0 @ sk_E_1))
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ X1 @ sk_H) @ X0)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 56.78/57.06      inference('sup-', [status(thm)], ['67', '72'])).
% 56.78/57.06  thf('74', plain, ((v1_relat_1 @ sk_E_1)),
% 56.78/57.06      inference('demod', [status(thm)], ['18', '19'])).
% 56.78/57.06  thf('75', plain,
% 56.78/57.06      ((![X0 : $i, X1 : $i]:
% 56.78/57.06          (~ (v1_relat_1 @ X0)
% 56.78/57.06           | (r2_hidden @ (k4_tarski @ X1 @ sk_G) @ (k5_relat_1 @ X0 @ sk_E_1))
% 56.78/57.06           | ~ (r2_hidden @ (k4_tarski @ X1 @ sk_H) @ X0)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 56.78/57.06      inference('demod', [status(thm)], ['73', '74'])).
% 56.78/57.06  thf('76', plain,
% 56.78/57.06      ((((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06          (k5_relat_1 @ sk_D_1 @ sk_E_1))
% 56.78/57.06         | ~ (v1_relat_1 @ sk_D_1)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) & 
% 56.78/57.06             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 56.78/57.06      inference('sup-', [status(thm)], ['66', '75'])).
% 56.78/57.06  thf('77', plain, ((v1_relat_1 @ sk_D_1)),
% 56.78/57.06      inference('demod', [status(thm)], ['23', '24'])).
% 56.78/57.06  thf('78', plain,
% 56.78/57.06      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06         (k5_relat_1 @ sk_D_1 @ sk_E_1)))
% 56.78/57.06         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) & 
% 56.78/57.06             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)))),
% 56.78/57.06      inference('demod', [status(thm)], ['76', '77'])).
% 56.78/57.06  thf('79', plain,
% 56.78/57.06      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)
% 56.78/57.06         = (k5_relat_1 @ sk_D_1 @ sk_E_1))),
% 56.78/57.06      inference('sup-', [status(thm)], ['5', '8'])).
% 56.78/57.06  thf('80', plain,
% 56.78/57.06      ((~ (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))
% 56.78/57.06         <= (~
% 56.78/57.06             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('split', [status(esa)], ['43'])).
% 56.78/57.06  thf('81', plain,
% 56.78/57.06      ((~ (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06           (k5_relat_1 @ sk_D_1 @ sk_E_1)))
% 56.78/57.06         <= (~
% 56.78/57.06             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))))),
% 56.78/57.06      inference('sup-', [status(thm)], ['79', '80'])).
% 56.78/57.06  thf('82', plain,
% 56.78/57.06      (~ ((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) | 
% 56.78/57.06       ~ ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_1)) | 
% 56.78/57.06       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 56.78/57.06         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D_1 @ sk_E_1)))),
% 56.78/57.06      inference('sup-', [status(thm)], ['78', '81'])).
% 56.78/57.06  thf('83', plain, ($false),
% 56.78/57.06      inference('sat_resolution*', [status(thm)],
% 56.78/57.06                ['1', '3', '56', '63', '64', '65', '82'])).
% 56.78/57.06  
% 56.78/57.06  % SZS output end Refutation
% 56.78/57.06  
% 56.78/57.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
