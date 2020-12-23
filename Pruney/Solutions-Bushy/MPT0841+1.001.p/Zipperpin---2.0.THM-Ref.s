%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0841+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EFPdv9D5VM

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:34 EST 2020

% Result     : Theorem 5.94s
% Output     : Refutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 194 expanded)
%              Number of leaves         :   25 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  871 (3123 expanded)
%              Number of equality atoms :    9 (  31 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t52_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ A )
                     => ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) )
                      <=> ? [F: $i] :
                            ( ( r2_hidden @ F @ B )
                            & ( r2_hidden @ ( k4_tarski @ F @ E ) @ D )
                            & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ~ ( v1_xboole_0 @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ A )
                       => ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) )
                        <=> ? [F: $i] :
                              ( ( r2_hidden @ F @ B )
                              & ( r2_hidden @ ( k4_tarski @ F @ E ) @ D )
                              & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relset_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k7_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k9_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k9_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X8 @ X4 @ X5 ) @ X8 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X8 @ X4 @ X5 ) @ X8 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( m1_subset_1 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('21',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('23',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ X20 @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('25',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('27',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('28',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X30 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('30',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X30 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_E_2 ) @ sk_D_1 )
        | ~ ( m1_subset_1 @ X0 @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C )
      | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('34',plain,(
    ! [X4: $i,X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k9_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( sk_E_1 @ X8 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('35',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( sk_E_1 @ X8 @ X4 @ X5 ) @ X4 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['25','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('47',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,(
    ! [X4: $i,X5: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X7
       != ( k9_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X5 )
      | ~ ( r2_hidden @ X10 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('50',plain,(
    ! [X4: $i,X5: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ X10 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X5 )
      | ( r2_hidden @ X9 @ ( k9_relat_1 @ X5 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('56',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X30 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','45','46','59'])).


%------------------------------------------------------------------------------
