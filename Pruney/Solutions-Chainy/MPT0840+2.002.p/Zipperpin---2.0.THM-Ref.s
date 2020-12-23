%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GZsfb0uNyD

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:21 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 320 expanded)
%              Number of leaves         :   31 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          : 1545 (5931 expanded)
%              Number of equality atoms :   14 (  29 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_2_type,type,(
    sk_F_2: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_H @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_H @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('5',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k4_relset_1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D_3 @ X0 )
        = ( k5_relat_1 @ sk_D_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 )
    = ( k5_relat_1 @ sk_D_3 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_3 @ sk_E_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( X16
       != ( k5_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X20 @ X17 @ X14 @ X15 ) @ X20 ) @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X20 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X17: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X20 ) @ ( k5_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X20 @ X17 @ X14 @ X15 ) @ X20 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( ~ ( v1_relat_1 @ sk_E_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) @ sk_G ) @ sk_E_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_3 @ sk_E_1 ) )
      | ~ ( v1_relat_1 @ sk_D_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) @ sk_G ) @ sk_E_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_3 @ sk_E_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['15','20','25'])).

thf('27',plain,
    ( ( ~ ( v1_relat_1 @ sk_E_1 )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) @ sk_G ) @ sk_E_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('29',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['23','24'])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) @ sk_G ) @ sk_E_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_3 @ sk_E_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( X16
       != ( k5_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_F_1 @ X20 @ X17 @ X14 @ X15 ) ) @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X20 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('34',plain,(
    ! [X14: $i,X15: $i,X17: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X20 ) @ ( k5_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_F_1 @ X20 @ X17 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ~ ( v1_relat_1 @ sk_E_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) ) @ sk_D_3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_3 @ sk_E_1 ) )
      | ~ ( v1_relat_1 @ sk_D_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['23','24'])).

thf('38',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) ) @ sk_D_3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_3 @ sk_E_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ~ ( v1_relat_1 @ sk_E_1 )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) ) @ sk_D_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['23','24'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X38: $i] :
      ( ~ ( m1_subset_1 @ X38 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
        | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 ) )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
        | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) @ sk_G ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) @ sk_B ) )
   <= ( ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
          | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k2_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k2_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( r2_hidden @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) @ ( k2_relat_1 @ sk_D_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('51',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X26 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('52',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_3 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','55'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r2_hidden @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('61',plain,
    ( ( m1_subset_1 @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3 ) @ sk_G ) @ sk_E_1 )
   <= ( ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
          | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ) ),
    inference(demod,[status(thm)],['45','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) )
    | ~ ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
          | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['30','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_H @ sk_B )
   <= ( m1_subset_1 @ sk_H @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('65',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('66',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
        | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 ) )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
        | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['43'])).

thf('68',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ sk_H @ sk_B ) )
   <= ( ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
          | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( m1_subset_1 @ sk_H @ sk_B )
   <= ( ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
          | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 )
    | ~ ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
          | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 ) )
    | ~ ( m1_subset_1 @ sk_H @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) )
    | ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ X38 ) @ sk_D_3 )
        | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_G ) @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['43'])).

thf('72',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('73',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( X16
       != ( k5_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X18 ) @ X14 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('77',plain,(
    ! [X14: $i,X15: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X18 ) @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X15 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ ( k5_relat_1 @ X15 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ sk_E_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_G ) @ ( k5_relat_1 @ X0 @ sk_E_1 ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ sk_H ) @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('82',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_G ) @ ( k5_relat_1 @ X0 @ sk_E_1 ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ sk_H ) @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_3 @ sk_E_1 ) )
      | ~ ( v1_relat_1 @ sk_D_3 ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['23','24'])).

thf('85',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_3 @ sk_E_1 ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 )
    = ( k5_relat_1 @ sk_D_3 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('87',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['43'])).

thf('88',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k5_relat_1 @ sk_D_3 @ sk_E_1 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_H @ sk_G ) @ sk_E_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_H ) @ sk_D_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_F_2 @ sk_G ) @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','63','70','71','72','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GZsfb0uNyD
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.07/1.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.26  % Solved by: fo/fo7.sh
% 1.07/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.26  % done 482 iterations in 0.801s
% 1.07/1.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.26  % SZS output start Refutation
% 1.07/1.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.26  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.07/1.26  thf(sk_D_3_type, type, sk_D_3: $i).
% 1.07/1.26  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 1.07/1.26  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.07/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.26  thf(sk_F_2_type, type, sk_F_2: $i).
% 1.07/1.26  thf(sk_E_1_type, type, sk_E_1: $i).
% 1.07/1.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.26  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.07/1.26  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.07/1.26  thf(sk_H_type, type, sk_H: $i).
% 1.07/1.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.26  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.07/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.26  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.07/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.07/1.26  thf(sk_G_type, type, sk_G: $i).
% 1.07/1.26  thf(t51_relset_1, conjecture,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.07/1.26       ( ![B:$i]:
% 1.07/1.26         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.07/1.26           ( ![C:$i]:
% 1.07/1.26             ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.07/1.26               ( ![D:$i]:
% 1.07/1.26                 ( ( m1_subset_1 @
% 1.07/1.26                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26                   ( ![E:$i]:
% 1.07/1.26                     ( ( m1_subset_1 @
% 1.07/1.26                         E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 1.07/1.26                       ( ![F:$i,G:$i]:
% 1.07/1.26                         ( ( r2_hidden @
% 1.07/1.26                             ( k4_tarski @ F @ G ) @ 
% 1.07/1.26                             ( k4_relset_1 @ A @ B @ B @ C @ D @ E ) ) <=>
% 1.07/1.26                           ( ?[H:$i]:
% 1.07/1.26                             ( ( r2_hidden @ ( k4_tarski @ H @ G ) @ E ) & 
% 1.07/1.26                               ( r2_hidden @ ( k4_tarski @ F @ H ) @ D ) & 
% 1.07/1.26                               ( m1_subset_1 @ H @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.07/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.26    (~( ![A:$i]:
% 1.07/1.26        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.07/1.26          ( ![B:$i]:
% 1.07/1.26            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.07/1.26              ( ![C:$i]:
% 1.07/1.26                ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.07/1.26                  ( ![D:$i]:
% 1.07/1.26                    ( ( m1_subset_1 @
% 1.07/1.26                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26                      ( ![E:$i]:
% 1.07/1.26                        ( ( m1_subset_1 @
% 1.07/1.26                            E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 1.07/1.26                          ( ![F:$i,G:$i]:
% 1.07/1.26                            ( ( r2_hidden @
% 1.07/1.26                                ( k4_tarski @ F @ G ) @ 
% 1.07/1.26                                ( k4_relset_1 @ A @ B @ B @ C @ D @ E ) ) <=>
% 1.07/1.26                              ( ?[H:$i]:
% 1.07/1.26                                ( ( r2_hidden @ ( k4_tarski @ H @ G ) @ E ) & 
% 1.07/1.26                                  ( r2_hidden @ ( k4_tarski @ F @ H ) @ D ) & 
% 1.07/1.26                                  ( m1_subset_1 @ H @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.07/1.26    inference('cnf.neg', [status(esa)], [t51_relset_1])).
% 1.07/1.26  thf('0', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3)
% 1.07/1.26        | (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('1', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3)) | 
% 1.07/1.26       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)))),
% 1.07/1.26      inference('split', [status(esa)], ['0'])).
% 1.07/1.26  thf('2', plain,
% 1.07/1.26      (((m1_subset_1 @ sk_H @ sk_B)
% 1.07/1.26        | (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('3', plain,
% 1.07/1.26      (((m1_subset_1 @ sk_H @ sk_B)) | 
% 1.07/1.26       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)))),
% 1.07/1.26      inference('split', [status(esa)], ['2'])).
% 1.07/1.26  thf(dt_k5_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.07/1.26       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.07/1.26  thf('4', plain,
% 1.07/1.26      (![X22 : $i, X23 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X22)
% 1.07/1.26          | ~ (v1_relat_1 @ X23)
% 1.07/1.26          | (v1_relat_1 @ (k5_relat_1 @ X22 @ X23)))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.07/1.26  thf('5', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('6', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(redefinition_k4_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.07/1.26     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.26         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.07/1.26       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.07/1.26  thf('7', plain,
% 1.07/1.26      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.07/1.26          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.07/1.26          | ((k4_relset_1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 1.07/1.26              = (k5_relat_1 @ X32 @ X35)))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.07/1.26  thf('8', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D_3 @ X0)
% 1.07/1.26            = (k5_relat_1 @ sk_D_3 @ X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['6', '7'])).
% 1.07/1.26  thf('9', plain,
% 1.07/1.26      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)
% 1.07/1.26         = (k5_relat_1 @ sk_D_3 @ sk_E_1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['5', '8'])).
% 1.07/1.26  thf('10', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)
% 1.07/1.26        | (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('11', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('split', [status(esa)], ['10'])).
% 1.07/1.26  thf('12', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26         (k5_relat_1 @ sk_D_3 @ sk_E_1)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('sup+', [status(thm)], ['9', '11'])).
% 1.07/1.26  thf(d8_relat_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ A ) =>
% 1.07/1.26       ( ![B:$i]:
% 1.07/1.26         ( ( v1_relat_1 @ B ) =>
% 1.07/1.26           ( ![C:$i]:
% 1.07/1.26             ( ( v1_relat_1 @ C ) =>
% 1.07/1.26               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 1.07/1.26                 ( ![D:$i,E:$i]:
% 1.07/1.26                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 1.07/1.26                     ( ?[F:$i]:
% 1.07/1.26                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 1.07/1.26                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 1.07/1.26  thf('13', plain,
% 1.07/1.26      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X20 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X14)
% 1.07/1.26          | ((X16) != (k5_relat_1 @ X15 @ X14))
% 1.07/1.26          | (r2_hidden @ 
% 1.07/1.26             (k4_tarski @ (sk_F_1 @ X20 @ X17 @ X14 @ X15) @ X20) @ X14)
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X17 @ X20) @ X16)
% 1.07/1.26          | ~ (v1_relat_1 @ X16)
% 1.07/1.26          | ~ (v1_relat_1 @ X15))),
% 1.07/1.26      inference('cnf', [status(esa)], [d8_relat_1])).
% 1.07/1.26  thf('14', plain,
% 1.07/1.26      (![X14 : $i, X15 : $i, X17 : $i, X20 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X15)
% 1.07/1.26          | ~ (v1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X17 @ X20) @ (k5_relat_1 @ X15 @ X14))
% 1.07/1.26          | (r2_hidden @ 
% 1.07/1.26             (k4_tarski @ (sk_F_1 @ X20 @ X17 @ X14 @ X15) @ X20) @ X14)
% 1.07/1.26          | ~ (v1_relat_1 @ X14))),
% 1.07/1.26      inference('simplify', [status(thm)], ['13'])).
% 1.07/1.26  thf('15', plain,
% 1.07/1.26      (((~ (v1_relat_1 @ sk_E_1)
% 1.07/1.26         | (r2_hidden @ 
% 1.07/1.26            (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3) @ sk_G) @ 
% 1.07/1.26            sk_E_1)
% 1.07/1.26         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_3 @ sk_E_1))
% 1.07/1.26         | ~ (v1_relat_1 @ sk_D_3)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['12', '14'])).
% 1.07/1.26  thf('16', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(cc2_relat_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ A ) =>
% 1.07/1.26       ( ![B:$i]:
% 1.07/1.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.07/1.26  thf('17', plain,
% 1.07/1.26      (![X5 : $i, X6 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 1.07/1.26          | (v1_relat_1 @ X5)
% 1.07/1.26          | ~ (v1_relat_1 @ X6))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.26  thf('18', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) | (v1_relat_1 @ sk_E_1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['16', '17'])).
% 1.07/1.26  thf(fc6_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.07/1.26  thf('19', plain,
% 1.07/1.26      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 1.07/1.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.26  thf('20', plain, ((v1_relat_1 @ sk_E_1)),
% 1.07/1.26      inference('demod', [status(thm)], ['18', '19'])).
% 1.07/1.26  thf('21', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('22', plain,
% 1.07/1.26      (![X5 : $i, X6 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 1.07/1.26          | (v1_relat_1 @ X5)
% 1.07/1.26          | ~ (v1_relat_1 @ X6))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.26  thf('23', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_3))),
% 1.07/1.26      inference('sup-', [status(thm)], ['21', '22'])).
% 1.07/1.26  thf('24', plain,
% 1.07/1.26      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 1.07/1.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.26  thf('25', plain, ((v1_relat_1 @ sk_D_3)),
% 1.07/1.26      inference('demod', [status(thm)], ['23', '24'])).
% 1.07/1.26  thf('26', plain,
% 1.07/1.26      ((((r2_hidden @ 
% 1.07/1.26          (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3) @ sk_G) @ 
% 1.07/1.26          sk_E_1)
% 1.07/1.26         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_3 @ sk_E_1))))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('demod', [status(thm)], ['15', '20', '25'])).
% 1.07/1.26  thf('27', plain,
% 1.07/1.26      (((~ (v1_relat_1 @ sk_E_1)
% 1.07/1.26         | ~ (v1_relat_1 @ sk_D_3)
% 1.07/1.26         | (r2_hidden @ 
% 1.07/1.26            (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3) @ sk_G) @ 
% 1.07/1.26            sk_E_1)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['4', '26'])).
% 1.07/1.26  thf('28', plain, ((v1_relat_1 @ sk_E_1)),
% 1.07/1.26      inference('demod', [status(thm)], ['18', '19'])).
% 1.07/1.26  thf('29', plain, ((v1_relat_1 @ sk_D_3)),
% 1.07/1.26      inference('demod', [status(thm)], ['23', '24'])).
% 1.07/1.26  thf('30', plain,
% 1.07/1.26      (((r2_hidden @ 
% 1.07/1.26         (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3) @ sk_G) @ 
% 1.07/1.26         sk_E_1))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.07/1.26  thf('31', plain,
% 1.07/1.26      (![X22 : $i, X23 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X22)
% 1.07/1.26          | ~ (v1_relat_1 @ X23)
% 1.07/1.26          | (v1_relat_1 @ (k5_relat_1 @ X22 @ X23)))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.07/1.26  thf('32', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26         (k5_relat_1 @ sk_D_3 @ sk_E_1)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('sup+', [status(thm)], ['9', '11'])).
% 1.07/1.26  thf('33', plain,
% 1.07/1.26      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X20 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X14)
% 1.07/1.26          | ((X16) != (k5_relat_1 @ X15 @ X14))
% 1.07/1.26          | (r2_hidden @ 
% 1.07/1.26             (k4_tarski @ X17 @ (sk_F_1 @ X20 @ X17 @ X14 @ X15)) @ X15)
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X17 @ X20) @ X16)
% 1.07/1.26          | ~ (v1_relat_1 @ X16)
% 1.07/1.26          | ~ (v1_relat_1 @ X15))),
% 1.07/1.26      inference('cnf', [status(esa)], [d8_relat_1])).
% 1.07/1.26  thf('34', plain,
% 1.07/1.26      (![X14 : $i, X15 : $i, X17 : $i, X20 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X15)
% 1.07/1.26          | ~ (v1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X17 @ X20) @ (k5_relat_1 @ X15 @ X14))
% 1.07/1.26          | (r2_hidden @ 
% 1.07/1.26             (k4_tarski @ X17 @ (sk_F_1 @ X20 @ X17 @ X14 @ X15)) @ X15)
% 1.07/1.26          | ~ (v1_relat_1 @ X14))),
% 1.07/1.26      inference('simplify', [status(thm)], ['33'])).
% 1.07/1.26  thf('35', plain,
% 1.07/1.26      (((~ (v1_relat_1 @ sk_E_1)
% 1.07/1.26         | (r2_hidden @ 
% 1.07/1.26            (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3)) @ 
% 1.07/1.26            sk_D_3)
% 1.07/1.26         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_3 @ sk_E_1))
% 1.07/1.26         | ~ (v1_relat_1 @ sk_D_3)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['32', '34'])).
% 1.07/1.26  thf('36', plain, ((v1_relat_1 @ sk_E_1)),
% 1.07/1.26      inference('demod', [status(thm)], ['18', '19'])).
% 1.07/1.26  thf('37', plain, ((v1_relat_1 @ sk_D_3)),
% 1.07/1.26      inference('demod', [status(thm)], ['23', '24'])).
% 1.07/1.26  thf('38', plain,
% 1.07/1.26      ((((r2_hidden @ 
% 1.07/1.26          (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3)) @ 
% 1.07/1.26          sk_D_3)
% 1.07/1.26         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_3 @ sk_E_1))))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.07/1.26  thf('39', plain,
% 1.07/1.26      (((~ (v1_relat_1 @ sk_E_1)
% 1.07/1.26         | ~ (v1_relat_1 @ sk_D_3)
% 1.07/1.26         | (r2_hidden @ 
% 1.07/1.26            (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3)) @ 
% 1.07/1.26            sk_D_3)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['31', '38'])).
% 1.07/1.26  thf('40', plain, ((v1_relat_1 @ sk_E_1)),
% 1.07/1.26      inference('demod', [status(thm)], ['18', '19'])).
% 1.07/1.26  thf('41', plain, ((v1_relat_1 @ sk_D_3)),
% 1.07/1.26      inference('demod', [status(thm)], ['23', '24'])).
% 1.07/1.26  thf('42', plain,
% 1.07/1.26      (((r2_hidden @ 
% 1.07/1.26         (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3)) @ 
% 1.07/1.26         sk_D_3))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.07/1.26  thf('43', plain,
% 1.07/1.26      (![X38 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1)
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('44', plain,
% 1.07/1.26      ((![X38 : $i]:
% 1.07/1.26          (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1)))
% 1.07/1.26         <= ((![X38 : $i]:
% 1.07/1.26                (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1))))),
% 1.07/1.26      inference('split', [status(esa)], ['43'])).
% 1.07/1.26  thf('45', plain,
% 1.07/1.26      (((~ (r2_hidden @ 
% 1.07/1.26            (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3) @ sk_G) @ 
% 1.07/1.26            sk_E_1)
% 1.07/1.26         | ~ (m1_subset_1 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3) @ sk_B)))
% 1.07/1.26         <= ((![X38 : $i]:
% 1.07/1.26                (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1))) & 
% 1.07/1.26             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['42', '44'])).
% 1.07/1.26  thf('46', plain,
% 1.07/1.26      (((r2_hidden @ 
% 1.07/1.26         (k4_tarski @ sk_F_2 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3)) @ 
% 1.07/1.26         sk_D_3))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.07/1.26  thf(d5_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.07/1.26       ( ![C:$i]:
% 1.07/1.26         ( ( r2_hidden @ C @ B ) <=>
% 1.07/1.26           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.07/1.26  thf('47', plain,
% 1.07/1.26      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.07/1.26         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 1.07/1.26          | (r2_hidden @ X8 @ X10)
% 1.07/1.26          | ((X10) != (k2_relat_1 @ X9)))),
% 1.07/1.26      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.07/1.26  thf('48', plain,
% 1.07/1.26      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.07/1.26         ((r2_hidden @ X8 @ (k2_relat_1 @ X9))
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9))),
% 1.07/1.26      inference('simplify', [status(thm)], ['47'])).
% 1.07/1.26  thf('49', plain,
% 1.07/1.26      (((r2_hidden @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3) @ 
% 1.07/1.26         (k2_relat_1 @ sk_D_3)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['46', '48'])).
% 1.07/1.26  thf('50', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(dt_k2_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.07/1.26  thf('51', plain,
% 1.07/1.26      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.07/1.26         ((m1_subset_1 @ (k2_relset_1 @ X26 @ X27 @ X28) @ (k1_zfmisc_1 @ X27))
% 1.07/1.26          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.07/1.26  thf('52', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_3) @ 
% 1.07/1.26        (k1_zfmisc_1 @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.26  thf('53', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(redefinition_k2_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.07/1.26  thf('54', plain,
% 1.07/1.26      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.07/1.26         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 1.07/1.26          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.26  thf('55', plain,
% 1.07/1.26      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 1.07/1.26      inference('sup-', [status(thm)], ['53', '54'])).
% 1.07/1.26  thf('56', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_relat_1 @ sk_D_3) @ (k1_zfmisc_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['52', '55'])).
% 1.07/1.26  thf(l3_subset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.07/1.26       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.07/1.26  thf('57', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X0 @ X1)
% 1.07/1.26          | (r2_hidden @ X0 @ X2)
% 1.07/1.26          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 1.07/1.26      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.07/1.26  thf('58', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['56', '57'])).
% 1.07/1.26  thf('59', plain,
% 1.07/1.26      (((r2_hidden @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3) @ sk_B))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['49', '58'])).
% 1.07/1.26  thf(t1_subset, axiom,
% 1.07/1.26    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.07/1.26  thf('60', plain,
% 1.07/1.26      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 1.07/1.26      inference('cnf', [status(esa)], [t1_subset])).
% 1.07/1.26  thf('61', plain,
% 1.07/1.26      (((m1_subset_1 @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3) @ sk_B))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['59', '60'])).
% 1.07/1.26  thf('62', plain,
% 1.07/1.26      ((~ (r2_hidden @ 
% 1.07/1.26           (k4_tarski @ (sk_F_1 @ sk_G @ sk_F_2 @ sk_E_1 @ sk_D_3) @ sk_G) @ 
% 1.07/1.26           sk_E_1))
% 1.07/1.26         <= ((![X38 : $i]:
% 1.07/1.26                (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1))) & 
% 1.07/1.26             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('demod', [status(thm)], ['45', '61'])).
% 1.07/1.26  thf('63', plain,
% 1.07/1.26      (~
% 1.07/1.26       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))) | 
% 1.07/1.26       ~
% 1.07/1.26       (![X38 : $i]:
% 1.07/1.26          (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['30', '62'])).
% 1.07/1.26  thf('64', plain,
% 1.07/1.26      (((m1_subset_1 @ sk_H @ sk_B)) <= (((m1_subset_1 @ sk_H @ sk_B)))),
% 1.07/1.26      inference('split', [status(esa)], ['2'])).
% 1.07/1.26  thf('65', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 1.07/1.26      inference('split', [status(esa)], ['10'])).
% 1.07/1.26  thf('66', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3)))),
% 1.07/1.26      inference('split', [status(esa)], ['0'])).
% 1.07/1.26  thf('67', plain,
% 1.07/1.26      ((![X38 : $i]:
% 1.07/1.26          (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1)))
% 1.07/1.26         <= ((![X38 : $i]:
% 1.07/1.26                (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1))))),
% 1.07/1.26      inference('split', [status(esa)], ['43'])).
% 1.07/1.26  thf('68', plain,
% 1.07/1.26      (((~ (r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)
% 1.07/1.26         | ~ (m1_subset_1 @ sk_H @ sk_B)))
% 1.07/1.26         <= ((![X38 : $i]:
% 1.07/1.26                (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1))) & 
% 1.07/1.26             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['66', '67'])).
% 1.07/1.26  thf('69', plain,
% 1.07/1.26      ((~ (m1_subset_1 @ sk_H @ sk_B))
% 1.07/1.26         <= ((![X38 : $i]:
% 1.07/1.26                (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26                 | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1))) & 
% 1.07/1.26             ((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) & 
% 1.07/1.26             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['65', '68'])).
% 1.07/1.26  thf('70', plain,
% 1.07/1.26      (~ ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3)) | 
% 1.07/1.26       ~
% 1.07/1.26       (![X38 : $i]:
% 1.07/1.26          (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1))) | 
% 1.07/1.26       ~ ((m1_subset_1 @ sk_H @ sk_B)) | 
% 1.07/1.26       ~ ((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['64', '69'])).
% 1.07/1.26  thf('71', plain,
% 1.07/1.26      (~
% 1.07/1.26       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))) | 
% 1.07/1.26       (![X38 : $i]:
% 1.07/1.26          (~ (m1_subset_1 @ X38 @ sk_B)
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ sk_F_2 @ X38) @ sk_D_3)
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_G) @ sk_E_1)))),
% 1.07/1.26      inference('split', [status(esa)], ['43'])).
% 1.07/1.26  thf('72', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) | 
% 1.07/1.26       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)))),
% 1.07/1.26      inference('split', [status(esa)], ['10'])).
% 1.07/1.26  thf('73', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3)))),
% 1.07/1.26      inference('split', [status(esa)], ['0'])).
% 1.07/1.26  thf('74', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 1.07/1.26      inference('split', [status(esa)], ['10'])).
% 1.07/1.26  thf('75', plain,
% 1.07/1.26      (![X22 : $i, X23 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X22)
% 1.07/1.26          | ~ (v1_relat_1 @ X23)
% 1.07/1.26          | (v1_relat_1 @ (k5_relat_1 @ X22 @ X23)))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.07/1.26  thf('76', plain,
% 1.07/1.26      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X14)
% 1.07/1.26          | ((X16) != (k5_relat_1 @ X15 @ X14))
% 1.07/1.26          | (r2_hidden @ (k4_tarski @ X17 @ X18) @ X16)
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ X15)
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X19 @ X18) @ X14)
% 1.07/1.26          | ~ (v1_relat_1 @ X16)
% 1.07/1.26          | ~ (v1_relat_1 @ X15))),
% 1.07/1.26      inference('cnf', [status(esa)], [d8_relat_1])).
% 1.07/1.26  thf('77', plain,
% 1.07/1.26      (![X14 : $i, X15 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X15)
% 1.07/1.26          | ~ (v1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X19 @ X18) @ X14)
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ X15)
% 1.07/1.26          | (r2_hidden @ (k4_tarski @ X17 @ X18) @ (k5_relat_1 @ X15 @ X14))
% 1.07/1.26          | ~ (v1_relat_1 @ X14))),
% 1.07/1.26      inference('simplify', [status(thm)], ['76'])).
% 1.07/1.26  thf('78', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X1)
% 1.07/1.26          | ~ (v1_relat_1 @ X0)
% 1.07/1.26          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['75', '77'])).
% 1.07/1.26  thf('79', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.07/1.26         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 1.07/1.26          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 1.07/1.26          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 1.07/1.26          | ~ (v1_relat_1 @ X1)
% 1.07/1.26          | ~ (v1_relat_1 @ X0))),
% 1.07/1.26      inference('simplify', [status(thm)], ['78'])).
% 1.07/1.26  thf('80', plain,
% 1.07/1.26      ((![X0 : $i, X1 : $i]:
% 1.07/1.26          (~ (v1_relat_1 @ sk_E_1)
% 1.07/1.26           | ~ (v1_relat_1 @ X0)
% 1.07/1.26           | (r2_hidden @ (k4_tarski @ X1 @ sk_G) @ (k5_relat_1 @ X0 @ sk_E_1))
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ X1 @ sk_H) @ X0)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['74', '79'])).
% 1.07/1.26  thf('81', plain, ((v1_relat_1 @ sk_E_1)),
% 1.07/1.26      inference('demod', [status(thm)], ['18', '19'])).
% 1.07/1.26  thf('82', plain,
% 1.07/1.26      ((![X0 : $i, X1 : $i]:
% 1.07/1.26          (~ (v1_relat_1 @ X0)
% 1.07/1.26           | (r2_hidden @ (k4_tarski @ X1 @ sk_G) @ (k5_relat_1 @ X0 @ sk_E_1))
% 1.07/1.26           | ~ (r2_hidden @ (k4_tarski @ X1 @ sk_H) @ X0)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)))),
% 1.07/1.26      inference('demod', [status(thm)], ['80', '81'])).
% 1.07/1.26  thf('83', plain,
% 1.07/1.26      ((((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26          (k5_relat_1 @ sk_D_3 @ sk_E_1))
% 1.07/1.26         | ~ (v1_relat_1 @ sk_D_3)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) & 
% 1.07/1.26             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['73', '82'])).
% 1.07/1.26  thf('84', plain, ((v1_relat_1 @ sk_D_3)),
% 1.07/1.26      inference('demod', [status(thm)], ['23', '24'])).
% 1.07/1.26  thf('85', plain,
% 1.07/1.26      (((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26         (k5_relat_1 @ sk_D_3 @ sk_E_1)))
% 1.07/1.26         <= (((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) & 
% 1.07/1.26             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3)))),
% 1.07/1.26      inference('demod', [status(thm)], ['83', '84'])).
% 1.07/1.26  thf('86', plain,
% 1.07/1.26      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)
% 1.07/1.26         = (k5_relat_1 @ sk_D_3 @ sk_E_1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['5', '8'])).
% 1.07/1.26  thf('87', plain,
% 1.07/1.26      ((~ (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('split', [status(esa)], ['43'])).
% 1.07/1.26  thf('88', plain,
% 1.07/1.26      ((~ (r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26           (k5_relat_1 @ sk_D_3 @ sk_E_1)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['86', '87'])).
% 1.07/1.26  thf('89', plain,
% 1.07/1.26      (~ ((r2_hidden @ (k4_tarski @ sk_H @ sk_G) @ sk_E_1)) | 
% 1.07/1.26       ~ ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_H) @ sk_D_3)) | 
% 1.07/1.26       ((r2_hidden @ (k4_tarski @ sk_F_2 @ sk_G) @ 
% 1.07/1.26         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C_1 @ sk_D_3 @ sk_E_1)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['85', '88'])).
% 1.07/1.26  thf('90', plain, ($false),
% 1.07/1.26      inference('sat_resolution*', [status(thm)],
% 1.07/1.26                ['1', '3', '63', '70', '71', '72', '89'])).
% 1.07/1.26  
% 1.07/1.26  % SZS output end Refutation
% 1.07/1.26  
% 1.07/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
