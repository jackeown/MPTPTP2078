%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BSZCbl7AKG

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:05 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  233 ( 778 expanded)
%              Number of leaves         :   39 ( 261 expanded)
%              Depth                    :   23
%              Number of atoms          : 1759 (8143 expanded)
%              Number of equality atoms :  148 ( 325 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t76_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
     => ! [E: $i] :
          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
         => ! [F: $i] :
              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) )
                 => ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) )
                   => ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D )
                      & ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E )
                      & ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
       => ! [E: $i] :
            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) )
               => ! [G: $i] :
                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) )
                   => ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) )
                     => ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D )
                        & ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E )
                        & ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X33 @ X34 @ X36 @ X35 )
        = ( k2_mcart_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k3_zfmisc_1 @ X33 @ X34 @ X36 ) )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('5',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X30 ) @ X32 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('16',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_F )
    | ( sk_C_1 = sk_F ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_F )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C_1 = sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X20: $i] :
      ( r1_tarski @ k1_xboole_0 @ X20 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C_1 = sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( k1_xboole_0 = sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['9','12'])).

thf('27',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X33 @ X34 @ X36 @ X35 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k3_zfmisc_1 @ X33 @ X34 @ X36 ) )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('29',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('31',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('34',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('38',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['31','38'])).

thf('40',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_F @ sk_C_1 )
    = sk_F ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( r1_xboole_0 @ sk_F @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_F @ k1_xboole_0 )
        | ( sk_B_1 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X20: $i] :
      ( r1_tarski @ k1_xboole_0 @ X20 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['26','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['53','54'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('56',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_E @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( ( k4_xboole_0 @ sk_E @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( sk_E = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('70',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('72',plain,
    ( ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ k1_xboole_0 @ sk_F ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('74',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X30 ) @ X32 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X20: $i] :
      ( r1_tarski @ k1_xboole_0 @ X20 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('77',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('82',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('95',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','97'])).

thf('99',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('102',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('105',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','107'])).

thf('109',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['72','108','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('116',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ k1_xboole_0 @ sk_E @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('118',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['111','112'])).

thf('123',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ),
    inference(demod,[status(thm)],['116','121','122'])).

thf('124',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('125',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('126',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X30 ) @ X32 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('127',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['9','12'])).

thf('129',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X33 @ X34 @ X36 @ X35 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k3_zfmisc_1 @ X33 @ X34 @ X36 ) )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('131',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['6'])).

thf('133',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['125','126'])).

thf('135',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( r1_xboole_0 @ sk_F @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_F @ k1_xboole_0 )
        | ( sk_B_1 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['128','139'])).

thf('141',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('142',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('143',plain,
    ( ( k3_xboole_0 @ sk_E @ sk_B_1 )
    = sk_E ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E )
      | ~ ( r1_xboole_0 @ sk_E @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_E @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['140','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['127','148'])).

thf('150',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf('151',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('152',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ~ ( r1_xboole_0 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_D @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['149','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('157',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ),
    inference('sup-',[status(thm)],['124','157'])).

thf('159',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('160',plain,(
    ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['123','158','159'])).

thf('161',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( k1_xboole_0 = sk_F ) ),
    inference(simpl_trail,[status(thm)],['25','160'])).

thf('162',plain,
    ( ( k3_xboole_0 @ sk_E @ sk_B_1 )
    = sk_E ),
    inference('sup-',[status(thm)],['141','142'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('164',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('167',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('170',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['162','169'])).

thf('171',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['125','126'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('173',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['170','173'])).

thf('175',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0 = sk_F )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['161','174'])).

thf('176',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['111','112'])).

thf('177',plain,
    ( ( k1_xboole_0 = sk_F )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['150','151'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('180',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('183',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['180','183'])).

thf('185',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0 = sk_F ) ),
    inference('sup-',[status(thm)],['177','184'])).

thf('186',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['111','112'])).

thf('187',plain,(
    k1_xboole_0 = sk_F ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','97'])).

thf('189',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['111','112'])).

thf('192',plain,(
    $false ),
    inference(demod,[status(thm)],['2','187','190','191'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BSZCbl7AKG
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 938 iterations in 0.339s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.80  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.58/0.80  thf(sk_F_type, type, sk_F: $i).
% 0.58/0.80  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.58/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.80  thf(sk_E_type, type, sk_E: $i).
% 0.58/0.80  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.58/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.58/0.80  thf(sk_G_type, type, sk_G: $i).
% 0.58/0.80  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.58/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.80  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.58/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(t76_mcart_1, conjecture,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.80       ( ![E:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.58/0.80           ( ![F:$i]:
% 0.58/0.80             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.58/0.80               ( ![G:$i]:
% 0.58/0.80                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.58/0.80                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.58/0.80                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.58/0.80                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.58/0.80                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.80          ( ![E:$i]:
% 0.58/0.80            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.58/0.80              ( ![F:$i]:
% 0.58/0.80                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.58/0.80                  ( ![G:$i]:
% 0.58/0.80                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.58/0.80                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.58/0.80                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.58/0.80                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.58/0.80                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.58/0.80  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(d1_xboole_0, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.80  thf('1', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.80  thf('2', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.58/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(t50_mcart_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.58/0.80          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.58/0.80          ( ~( ![D:$i]:
% 0.58/0.80               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.58/0.80                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.58/0.80                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.58/0.80                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.58/0.80                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.58/0.80                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('4', plain,
% 0.58/0.80      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.80         (((X33) = (k1_xboole_0))
% 0.58/0.80          | ((X34) = (k1_xboole_0))
% 0.58/0.80          | ((k7_mcart_1 @ X33 @ X34 @ X36 @ X35) = (k2_mcart_1 @ X35))
% 0.58/0.80          | ~ (m1_subset_1 @ X35 @ (k3_zfmisc_1 @ X33 @ X34 @ X36))
% 0.58/0.80          | ((X36) = (k1_xboole_0)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.58/0.80  thf('5', plain,
% 0.58/0.80      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.80        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.58/0.80        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['3', '4'])).
% 0.58/0.80  thf('6', plain,
% 0.58/0.80      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)
% 0.58/0.80        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)
% 0.58/0.80        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('7', plain,
% 0.58/0.80      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.58/0.80      inference('split', [status(esa)], ['6'])).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.58/0.80         | ((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80         | ((sk_C_1) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['5', '7'])).
% 0.58/0.80  thf('9', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(d3_zfmisc_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.58/0.80       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.80         ((k3_zfmisc_1 @ X27 @ X28 @ X29)
% 0.58/0.80           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28) @ X29))),
% 0.58/0.80      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.58/0.80  thf(t10_mcart_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.58/0.80       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.58/0.80         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.58/0.80  thf('11', plain,
% 0.58/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.80         ((r2_hidden @ (k2_mcart_1 @ X30) @ X32)
% 0.58/0.80          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.58/0.80  thf('12', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.58/0.80          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.80  thf('13', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.58/0.80      inference('sup-', [status(thm)], ['9', '12'])).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (((((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80         | ((sk_C_1) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.58/0.80      inference('demod', [status(thm)], ['8', '13'])).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      (((((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80         | ((sk_C_1) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.58/0.80      inference('demod', [status(thm)], ['8', '13'])).
% 0.58/0.80  thf('16', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_1))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(t3_subset, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      (![X24 : $i, X25 : $i]:
% 0.58/0.80         ((r1_tarski @ X24 @ X25) | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.80  thf('18', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.58/0.80      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.80  thf(d10_xboole_0, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.80  thf('19', plain,
% 0.58/0.80      (![X9 : $i, X11 : $i]:
% 0.58/0.80         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 0.58/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.80  thf('20', plain, ((~ (r1_tarski @ sk_C_1 @ sk_F) | ((sk_C_1) = (sk_F)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.80  thf('21', plain,
% 0.58/0.80      (((~ (r1_tarski @ k1_xboole_0 @ sk_F)
% 0.58/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80         | ((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_C_1) = (sk_F))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['15', '20'])).
% 0.58/0.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.80  thf('22', plain, (![X20 : $i]: (r1_tarski @ k1_xboole_0 @ X20)),
% 0.58/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      (((((sk_B_1) = (k1_xboole_0))
% 0.58/0.80         | ((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_C_1) = (sk_F))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.58/0.80      inference('demod', [status(thm)], ['21', '22'])).
% 0.58/0.80  thf('24', plain,
% 0.58/0.80      (((((k1_xboole_0) = (sk_F))
% 0.58/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80         | ((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_B_1) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['14', '23'])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      (((((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80         | ((k1_xboole_0) = (sk_F))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.58/0.80      inference('simplify', [status(thm)], ['24'])).
% 0.58/0.80  thf('26', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.58/0.80      inference('sup-', [status(thm)], ['9', '12'])).
% 0.58/0.80  thf('27', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.80         (((X33) = (k1_xboole_0))
% 0.58/0.80          | ((X34) = (k1_xboole_0))
% 0.58/0.80          | ((k5_mcart_1 @ X33 @ X34 @ X36 @ X35)
% 0.58/0.80              = (k1_mcart_1 @ (k1_mcart_1 @ X35)))
% 0.58/0.80          | ~ (m1_subset_1 @ X35 @ (k3_zfmisc_1 @ X33 @ X34 @ X36))
% 0.58/0.80          | ((X36) = (k1_xboole_0)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.58/0.80  thf('29', plain,
% 0.58/0.80      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.80        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G)
% 0.58/0.80            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.58/0.80        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['27', '28'])).
% 0.58/0.80  thf('30', plain,
% 0.58/0.80      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('split', [status(esa)], ['6'])).
% 0.58/0.80  thf('31', plain,
% 0.58/0.80      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.58/0.80         | ((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80         | ((sk_C_1) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.80  thf('32', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('33', plain,
% 0.58/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.80         ((k3_zfmisc_1 @ X27 @ X28 @ X29)
% 0.58/0.80           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28) @ X29))),
% 0.58/0.80      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.58/0.80  thf('34', plain,
% 0.58/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.80         ((r2_hidden @ (k1_mcart_1 @ X30) @ X31)
% 0.58/0.80          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.58/0.80  thf('35', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.58/0.80          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.80  thf('36', plain,
% 0.58/0.80      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.58/0.80      inference('sup-', [status(thm)], ['32', '35'])).
% 0.58/0.80  thf('37', plain,
% 0.58/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.80         ((r2_hidden @ (k1_mcart_1 @ X30) @ X31)
% 0.58/0.80          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.58/0.80  thf('38', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.58/0.80      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.80  thf('39', plain,
% 0.58/0.80      (((((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80         | ((sk_C_1) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('demod', [status(thm)], ['31', '38'])).
% 0.58/0.80  thf('40', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.58/0.80      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.80  thf(t28_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.80  thf('41', plain,
% 0.58/0.80      (![X18 : $i, X19 : $i]:
% 0.58/0.80         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.58/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.80  thf('42', plain, (((k3_xboole_0 @ sk_F @ sk_C_1) = (sk_F))),
% 0.58/0.80      inference('sup-', [status(thm)], ['40', '41'])).
% 0.58/0.80  thf(t4_xboole_0, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.58/0.80            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.58/0.80  thf('43', plain,
% 0.58/0.80      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.58/0.80          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.80  thf('44', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X0 @ sk_F) | ~ (r1_xboole_0 @ sk_F @ sk_C_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.80  thf('45', plain,
% 0.58/0.80      ((![X0 : $i]:
% 0.58/0.80          (~ (r1_xboole_0 @ sk_F @ k1_xboole_0)
% 0.58/0.80           | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80           | ((sk_A) = (k1_xboole_0))
% 0.58/0.80           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['39', '44'])).
% 0.58/0.80  thf('46', plain, (![X20 : $i]: (r1_tarski @ k1_xboole_0 @ X20)),
% 0.58/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.80  thf(t106_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.58/0.80       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.58/0.80  thf('47', plain,
% 0.58/0.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X15 @ X17)
% 0.58/0.80          | ~ (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X17)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.58/0.80  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.58/0.80      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.80  thf(symmetry_r1_xboole_0, axiom,
% 0.58/0.80    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.58/0.80  thf('49', plain,
% 0.58/0.80      (![X3 : $i, X4 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.58/0.80  thf('50', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.58/0.80      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.80  thf('51', plain,
% 0.58/0.80      ((![X0 : $i]:
% 0.58/0.80          (((sk_B_1) = (k1_xboole_0))
% 0.58/0.80           | ((sk_A) = (k1_xboole_0))
% 0.58/0.80           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('demod', [status(thm)], ['45', '50'])).
% 0.58/0.80  thf('52', plain,
% 0.58/0.80      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['26', '51'])).
% 0.58/0.80  thf('53', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('54', plain,
% 0.58/0.80      (![X24 : $i, X25 : $i]:
% 0.58/0.80         ((r1_tarski @ X24 @ X25) | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.80  thf('55', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.58/0.80      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.80  thf(l32_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.80  thf('56', plain,
% 0.58/0.80      (![X12 : $i, X14 : $i]:
% 0.58/0.80         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.58/0.80          | ~ (r1_tarski @ X12 @ X14))),
% 0.58/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.80  thf('57', plain, (((k4_xboole_0 @ sk_E @ sk_B_1) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['55', '56'])).
% 0.58/0.80  thf('58', plain,
% 0.58/0.80      (((((k4_xboole_0 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 0.58/0.80         | ((sk_A) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['52', '57'])).
% 0.58/0.80  thf('59', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.58/0.80      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.80  thf(t83_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.80  thf('60', plain,
% 0.58/0.80      (![X21 : $i, X22 : $i]:
% 0.58/0.80         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 0.58/0.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.58/0.80  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['59', '60'])).
% 0.58/0.80  thf('62', plain,
% 0.58/0.80      (((((sk_E) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('demod', [status(thm)], ['58', '61'])).
% 0.58/0.80  thf('63', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('64', plain,
% 0.58/0.80      (![X24 : $i, X25 : $i]:
% 0.58/0.80         ((r1_tarski @ X24 @ X25) | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.80  thf('65', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.58/0.80      inference('sup-', [status(thm)], ['63', '64'])).
% 0.58/0.80  thf('66', plain,
% 0.58/0.80      (![X12 : $i, X14 : $i]:
% 0.58/0.80         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.58/0.80          | ~ (r1_tarski @ X12 @ X14))),
% 0.58/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.80  thf('67', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.80  thf('68', plain,
% 0.58/0.80      (((((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k1_xboole_0))
% 0.58/0.80         | ((sk_E) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['62', '67'])).
% 0.58/0.80  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['59', '60'])).
% 0.58/0.80  thf('70', plain,
% 0.58/0.80      (((((sk_D) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('demod', [status(thm)], ['68', '69'])).
% 0.58/0.80  thf('71', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.58/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.80  thf('72', plain,
% 0.58/0.80      (((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ k1_xboole_0 @ sk_F))
% 0.58/0.80         | ((sk_D) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['70', '71'])).
% 0.58/0.80  thf('73', plain,
% 0.58/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.80  thf('74', plain,
% 0.58/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.80         ((r2_hidden @ (k2_mcart_1 @ X30) @ X32)
% 0.58/0.80          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.58/0.80  thf('75', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.58/0.80          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['73', '74'])).
% 0.58/0.80  thf('76', plain, (![X20 : $i]: (r1_tarski @ k1_xboole_0 @ X20)),
% 0.58/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.80  thf('77', plain,
% 0.58/0.80      (![X18 : $i, X19 : $i]:
% 0.58/0.80         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.58/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.80  thf('78', plain,
% 0.58/0.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['76', '77'])).
% 0.58/0.80  thf('79', plain,
% 0.58/0.80      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.58/0.80          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.80  thf('80', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['78', '79'])).
% 0.58/0.80  thf('81', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.58/0.80      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.80  thf('82', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.58/0.80      inference('demod', [status(thm)], ['80', '81'])).
% 0.58/0.80  thf('83', plain,
% 0.58/0.80      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['75', '82'])).
% 0.58/0.80  thf('84', plain,
% 0.58/0.80      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.58/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.80  thf('85', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.58/0.80      inference('simplify', [status(thm)], ['84'])).
% 0.58/0.80  thf('86', plain,
% 0.58/0.80      (![X18 : $i, X19 : $i]:
% 0.58/0.80         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.58/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.80  thf('87', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['85', '86'])).
% 0.58/0.80  thf('88', plain,
% 0.58/0.80      (![X5 : $i, X6 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X5 @ X6)
% 0.58/0.80          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.80  thf('89', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.80  thf('90', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['88', '89'])).
% 0.58/0.80  thf('91', plain,
% 0.58/0.80      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['87', '90'])).
% 0.58/0.80  thf('92', plain,
% 0.58/0.80      (![X21 : $i, X22 : $i]:
% 0.58/0.80         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 0.58/0.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.58/0.80  thf('93', plain,
% 0.58/0.80      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_xboole_0 @ X0 @ X0) = (X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['91', '92'])).
% 0.58/0.80  thf('94', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.58/0.80      inference('simplify', [status(thm)], ['84'])).
% 0.58/0.80  thf('95', plain,
% 0.58/0.80      (![X12 : $i, X14 : $i]:
% 0.58/0.80         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.58/0.80          | ~ (r1_tarski @ X12 @ X14))),
% 0.58/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.80  thf('96', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['94', '95'])).
% 0.58/0.80  thf('97', plain,
% 0.58/0.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['93', '96'])).
% 0.58/0.80  thf('98', plain,
% 0.58/0.80      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['83', '97'])).
% 0.58/0.80  thf('99', plain,
% 0.58/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.80         ((k3_zfmisc_1 @ X27 @ X28 @ X29)
% 0.58/0.80           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28) @ X29))),
% 0.58/0.80      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.58/0.80  thf('100', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 0.58/0.80           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['98', '99'])).
% 0.58/0.80  thf('101', plain,
% 0.58/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.80  thf('102', plain,
% 0.58/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.80         ((r2_hidden @ (k1_mcart_1 @ X30) @ X31)
% 0.58/0.80          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.58/0.80  thf('103', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.58/0.80          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['101', '102'])).
% 0.58/0.80  thf('104', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.58/0.80      inference('demod', [status(thm)], ['80', '81'])).
% 0.58/0.80  thf('105', plain,
% 0.58/0.80      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['103', '104'])).
% 0.58/0.80  thf('106', plain,
% 0.58/0.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['93', '96'])).
% 0.58/0.80  thf('107', plain,
% 0.58/0.80      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['105', '106'])).
% 0.58/0.80  thf('108', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.80      inference('demod', [status(thm)], ['100', '107'])).
% 0.58/0.80  thf('109', plain,
% 0.58/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.80  thf('110', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['78', '79'])).
% 0.58/0.80  thf('111', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['109', '110'])).
% 0.58/0.80  thf('112', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.58/0.80      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.80  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.80      inference('demod', [status(thm)], ['111', '112'])).
% 0.58/0.80  thf('114', plain,
% 0.58/0.80      ((((sk_D) = (k1_xboole_0)))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('demod', [status(thm)], ['72', '108', '113'])).
% 0.58/0.80  thf('115', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.58/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.80  thf('116', plain,
% 0.58/0.80      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ k1_xboole_0 @ sk_E @ sk_F)))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['114', '115'])).
% 0.58/0.80  thf('117', plain,
% 0.58/0.80      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['105', '106'])).
% 0.58/0.80  thf('118', plain,
% 0.58/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.80         ((k3_zfmisc_1 @ X27 @ X28 @ X29)
% 0.58/0.80           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28) @ X29))),
% 0.58/0.80      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.58/0.80  thf('119', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 0.58/0.80           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['117', '118'])).
% 0.58/0.80  thf('120', plain,
% 0.58/0.80      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['105', '106'])).
% 0.58/0.80  thf('121', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.58/0.80      inference('demod', [status(thm)], ['119', '120'])).
% 0.58/0.80  thf('122', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.80      inference('demod', [status(thm)], ['111', '112'])).
% 0.58/0.80  thf('123', plain,
% 0.58/0.80      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D))),
% 0.58/0.80      inference('demod', [status(thm)], ['116', '121', '122'])).
% 0.58/0.80  thf('124', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.58/0.80      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.80  thf('125', plain,
% 0.58/0.80      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.58/0.80      inference('sup-', [status(thm)], ['32', '35'])).
% 0.58/0.80  thf('126', plain,
% 0.58/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.80         ((r2_hidden @ (k2_mcart_1 @ X30) @ X32)
% 0.58/0.80          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.58/0.80  thf('127', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.58/0.80      inference('sup-', [status(thm)], ['125', '126'])).
% 0.58/0.80  thf('128', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.58/0.80      inference('sup-', [status(thm)], ['9', '12'])).
% 0.58/0.80  thf('129', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('130', plain,
% 0.58/0.80      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.80         (((X33) = (k1_xboole_0))
% 0.58/0.80          | ((X34) = (k1_xboole_0))
% 0.58/0.80          | ((k6_mcart_1 @ X33 @ X34 @ X36 @ X35)
% 0.58/0.80              = (k2_mcart_1 @ (k1_mcart_1 @ X35)))
% 0.58/0.80          | ~ (m1_subset_1 @ X35 @ (k3_zfmisc_1 @ X33 @ X34 @ X36))
% 0.58/0.80          | ((X36) = (k1_xboole_0)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.58/0.80  thf('131', plain,
% 0.58/0.80      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.80        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G)
% 0.58/0.80            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.58/0.80        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['129', '130'])).
% 0.58/0.80  thf('132', plain,
% 0.58/0.80      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.58/0.80      inference('split', [status(esa)], ['6'])).
% 0.58/0.80  thf('133', plain,
% 0.58/0.80      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.58/0.80         | ((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80         | ((sk_C_1) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['131', '132'])).
% 0.58/0.80  thf('134', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.58/0.80      inference('sup-', [status(thm)], ['125', '126'])).
% 0.58/0.80  thf('135', plain,
% 0.58/0.80      (((((sk_A) = (k1_xboole_0))
% 0.58/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80         | ((sk_C_1) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.58/0.80      inference('demod', [status(thm)], ['133', '134'])).
% 0.58/0.80  thf('136', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X0 @ sk_F) | ~ (r1_xboole_0 @ sk_F @ sk_C_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.80  thf('137', plain,
% 0.58/0.80      ((![X0 : $i]:
% 0.58/0.80          (~ (r1_xboole_0 @ sk_F @ k1_xboole_0)
% 0.58/0.80           | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80           | ((sk_A) = (k1_xboole_0))
% 0.58/0.80           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['135', '136'])).
% 0.58/0.80  thf('138', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.58/0.80      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.80  thf('139', plain,
% 0.58/0.80      ((![X0 : $i]:
% 0.58/0.80          (((sk_B_1) = (k1_xboole_0))
% 0.58/0.80           | ((sk_A) = (k1_xboole_0))
% 0.58/0.80           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.58/0.80      inference('demod', [status(thm)], ['137', '138'])).
% 0.58/0.80  thf('140', plain,
% 0.58/0.80      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['128', '139'])).
% 0.58/0.80  thf('141', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.58/0.80      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.80  thf('142', plain,
% 0.58/0.80      (![X18 : $i, X19 : $i]:
% 0.58/0.80         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.58/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.80  thf('143', plain, (((k3_xboole_0 @ sk_E @ sk_B_1) = (sk_E))),
% 0.58/0.80      inference('sup-', [status(thm)], ['141', '142'])).
% 0.58/0.80  thf('144', plain,
% 0.58/0.80      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.58/0.80          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.80  thf('145', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X0 @ sk_E) | ~ (r1_xboole_0 @ sk_E @ sk_B_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['143', '144'])).
% 0.58/0.80  thf('146', plain,
% 0.58/0.80      ((![X0 : $i]:
% 0.58/0.80          (~ (r1_xboole_0 @ sk_E @ k1_xboole_0)
% 0.58/0.80           | ((sk_A) = (k1_xboole_0))
% 0.58/0.80           | ~ (r2_hidden @ X0 @ sk_E)))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['140', '145'])).
% 0.58/0.80  thf('147', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.58/0.80      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.80  thf('148', plain,
% 0.58/0.80      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E)))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.58/0.80      inference('demod', [status(thm)], ['146', '147'])).
% 0.58/0.80  thf('149', plain,
% 0.58/0.80      ((((sk_A) = (k1_xboole_0)))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['127', '148'])).
% 0.58/0.80  thf('150', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.58/0.80      inference('sup-', [status(thm)], ['63', '64'])).
% 0.58/0.80  thf('151', plain,
% 0.58/0.80      (![X18 : $i, X19 : $i]:
% 0.58/0.80         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.58/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.80  thf('152', plain, (((k3_xboole_0 @ sk_D @ sk_A) = (sk_D))),
% 0.58/0.80      inference('sup-', [status(thm)], ['150', '151'])).
% 0.58/0.80  thf('153', plain,
% 0.58/0.80      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.58/0.80          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.80  thf('154', plain,
% 0.58/0.80      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_D) | ~ (r1_xboole_0 @ sk_D @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['152', '153'])).
% 0.58/0.80  thf('155', plain,
% 0.58/0.80      ((![X0 : $i]:
% 0.58/0.80          (~ (r1_xboole_0 @ sk_D @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['149', '154'])).
% 0.58/0.80  thf('156', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.58/0.80      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.80  thf('157', plain,
% 0.58/0.80      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.58/0.80         <= (~
% 0.58/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.58/0.80      inference('demod', [status(thm)], ['155', '156'])).
% 0.58/0.80  thf('158', plain,
% 0.58/0.80      (((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E))),
% 0.58/0.80      inference('sup-', [status(thm)], ['124', '157'])).
% 0.58/0.80  thf('159', plain,
% 0.58/0.80      (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)) | 
% 0.58/0.80       ~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)) | 
% 0.58/0.80       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D))),
% 0.58/0.80      inference('split', [status(esa)], ['6'])).
% 0.58/0.80  thf('160', plain,
% 0.58/0.80      (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F))),
% 0.58/0.80      inference('sat_resolution*', [status(thm)], ['123', '158', '159'])).
% 0.58/0.80  thf('161', plain,
% 0.58/0.80      ((((sk_A) = (k1_xboole_0))
% 0.58/0.80        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.80        | ((k1_xboole_0) = (sk_F)))),
% 0.58/0.80      inference('simpl_trail', [status(thm)], ['25', '160'])).
% 0.58/0.80  thf('162', plain, (((k3_xboole_0 @ sk_E @ sk_B_1) = (sk_E))),
% 0.58/0.80      inference('sup-', [status(thm)], ['141', '142'])).
% 0.58/0.80  thf('163', plain,
% 0.58/0.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['93', '96'])).
% 0.58/0.80  thf('164', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.58/0.80      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.80  thf('165', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['163', '164'])).
% 0.58/0.80  thf('166', plain,
% 0.58/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.80  thf('167', plain,
% 0.58/0.80      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.58/0.80          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.80  thf('168', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['166', '167'])).
% 0.58/0.80  thf('169', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['165', '168'])).
% 0.58/0.80  thf('170', plain, (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.58/0.80      inference('sup+', [status(thm)], ['162', '169'])).
% 0.58/0.80  thf('171', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.58/0.80      inference('sup-', [status(thm)], ['125', '126'])).
% 0.58/0.80  thf('172', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.80  thf('173', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.58/0.80      inference('sup-', [status(thm)], ['171', '172'])).
% 0.58/0.80  thf('174', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.80      inference('clc', [status(thm)], ['170', '173'])).
% 0.58/0.80  thf('175', plain,
% 0.58/0.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.80        | ((k1_xboole_0) = (sk_F))
% 0.58/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['161', '174'])).
% 0.58/0.80  thf('176', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.80      inference('demod', [status(thm)], ['111', '112'])).
% 0.58/0.80  thf('177', plain, ((((k1_xboole_0) = (sk_F)) | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.80      inference('demod', [status(thm)], ['175', '176'])).
% 0.58/0.80  thf('178', plain, (((k3_xboole_0 @ sk_D @ sk_A) = (sk_D))),
% 0.58/0.80      inference('sup-', [status(thm)], ['150', '151'])).
% 0.58/0.80  thf('179', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['165', '168'])).
% 0.58/0.80  thf('180', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.58/0.80      inference('sup+', [status(thm)], ['178', '179'])).
% 0.58/0.80  thf('181', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.58/0.80      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.80  thf('182', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.80  thf('183', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.58/0.80      inference('sup-', [status(thm)], ['181', '182'])).
% 0.58/0.80  thf('184', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.58/0.80      inference('clc', [status(thm)], ['180', '183'])).
% 0.58/0.80  thf('185', plain,
% 0.58/0.80      ((~ (v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (sk_F)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['177', '184'])).
% 0.58/0.80  thf('186', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.80      inference('demod', [status(thm)], ['111', '112'])).
% 0.58/0.80  thf('187', plain, (((k1_xboole_0) = (sk_F))),
% 0.58/0.80      inference('demod', [status(thm)], ['185', '186'])).
% 0.58/0.80  thf('188', plain,
% 0.58/0.80      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['83', '97'])).
% 0.58/0.80  thf('189', plain,
% 0.58/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.80         ((k3_zfmisc_1 @ X27 @ X28 @ X29)
% 0.58/0.80           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28) @ X29))),
% 0.58/0.80      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.58/0.80  thf('190', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['188', '189'])).
% 0.58/0.80  thf('191', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.80      inference('demod', [status(thm)], ['111', '112'])).
% 0.58/0.80  thf('192', plain, ($false),
% 0.58/0.80      inference('demod', [status(thm)], ['2', '187', '190', '191'])).
% 0.58/0.80  
% 0.58/0.80  % SZS output end Refutation
% 0.58/0.80  
% 0.58/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
