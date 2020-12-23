%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CYwJXI7XQm

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:49 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 253 expanded)
%              Number of leaves         :   33 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          : 1145 (3564 expanded)
%              Number of equality atoms :   19 (  95 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( X22
       != ( k1_funct_1 @ X21 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ ( k1_funct_1 @ X21 @ X20 ) ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k9_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( sk_D @ X19 @ X17 @ X18 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('13',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['20','21','26'])).

thf('28',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('30',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_relset_1,axiom,(
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

thf('32',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X46: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_hidden @ X46 @ ( k7_relset_1 @ X43 @ X44 @ X42 @ X41 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X46 @ X42 @ X43 @ X41 ) @ X46 ) @ X42 )
      | ~ ( m1_subset_1 @ X46 @ X44 )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_E ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X30 @ X31 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_E ) @ sk_D_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ X21 )
      | ( X22
        = ( k1_funct_1 @ X21 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('48',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('51',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X46: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_hidden @ X46 @ ( k7_relset_1 @ X43 @ X44 @ X42 @ X41 ) )
      | ( m1_subset_1 @ ( sk_F @ X46 @ X42 @ X43 @ X41 ) @ X43 )
      | ~ ( m1_subset_1 @ X46 @ X44 )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','42'])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('60',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X46: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_hidden @ X46 @ ( k7_relset_1 @ X43 @ X44 @ X42 @ X41 ) )
      | ( r2_hidden @ ( sk_F @ X46 @ X42 @ X43 @ X41 ) @ X41 )
      | ~ ( m1_subset_1 @ X46 @ X44 )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','42'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X47: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X47 ) )
      | ~ ( r2_hidden @ X47 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X47 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('75',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k9_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( sk_D @ X19 @ X17 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['73','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('85',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('89',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X25 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['87','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['27','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CYwJXI7XQm
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.13/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.13/1.34  % Solved by: fo/fo7.sh
% 1.13/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.34  % done 916 iterations in 0.877s
% 1.13/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.13/1.34  % SZS output start Refutation
% 1.13/1.34  thf(sk_B_type, type, sk_B: $i > $i).
% 1.13/1.34  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.13/1.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.13/1.34  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 1.13/1.34  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.13/1.34  thf(sk_E_type, type, sk_E: $i).
% 1.13/1.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.13/1.34  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.13/1.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.13/1.34  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.13/1.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.13/1.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.13/1.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.13/1.34  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.13/1.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.13/1.34  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.13/1.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.13/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.34  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.13/1.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.13/1.34  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.13/1.34  thf(d1_xboole_0, axiom,
% 1.13/1.34    (![A:$i]:
% 1.13/1.34     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.13/1.34  thf('0', plain,
% 1.13/1.34      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.13/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.13/1.34  thf(t8_funct_1, axiom,
% 1.13/1.34    (![A:$i,B:$i,C:$i]:
% 1.13/1.34     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.13/1.34       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.13/1.34         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.13/1.34           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.13/1.34  thf('1', plain,
% 1.13/1.34      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.13/1.34         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 1.13/1.34          | ((X22) != (k1_funct_1 @ X21 @ X20))
% 1.13/1.34          | (r2_hidden @ (k4_tarski @ X20 @ X22) @ X21)
% 1.13/1.34          | ~ (v1_funct_1 @ X21)
% 1.13/1.34          | ~ (v1_relat_1 @ X21))),
% 1.13/1.34      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.13/1.34  thf('2', plain,
% 1.13/1.34      (![X20 : $i, X21 : $i]:
% 1.13/1.34         (~ (v1_relat_1 @ X21)
% 1.13/1.34          | ~ (v1_funct_1 @ X21)
% 1.13/1.34          | (r2_hidden @ (k4_tarski @ X20 @ (k1_funct_1 @ X21 @ X20)) @ X21)
% 1.13/1.34          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X21)))),
% 1.13/1.34      inference('simplify', [status(thm)], ['1'])).
% 1.13/1.34  thf('3', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.13/1.34          | (r2_hidden @ 
% 1.13/1.34             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 1.13/1.34              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 1.13/1.34             X0)
% 1.13/1.34          | ~ (v1_funct_1 @ X0)
% 1.13/1.34          | ~ (v1_relat_1 @ X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['0', '2'])).
% 1.13/1.34  thf('4', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.13/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.13/1.34  thf('5', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         (~ (v1_relat_1 @ X0)
% 1.13/1.34          | ~ (v1_funct_1 @ X0)
% 1.13/1.34          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.13/1.34          | ~ (v1_xboole_0 @ X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['3', '4'])).
% 1.13/1.34  thf('6', plain,
% 1.13/1.34      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.13/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.13/1.34  thf(t143_relat_1, axiom,
% 1.13/1.34    (![A:$i,B:$i,C:$i]:
% 1.13/1.34     ( ( v1_relat_1 @ C ) =>
% 1.13/1.34       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.13/1.34         ( ?[D:$i]:
% 1.13/1.34           ( ( r2_hidden @ D @ B ) & 
% 1.13/1.34             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.13/1.34             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.13/1.34  thf('7', plain,
% 1.13/1.34      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.13/1.34         (~ (r2_hidden @ X18 @ (k9_relat_1 @ X19 @ X17))
% 1.13/1.34          | (r2_hidden @ (sk_D @ X19 @ X17 @ X18) @ (k1_relat_1 @ X19))
% 1.13/1.34          | ~ (v1_relat_1 @ X19))),
% 1.13/1.34      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.13/1.34  thf('8', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 1.13/1.34          | ~ (v1_relat_1 @ X1)
% 1.13/1.34          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 1.13/1.34             (k1_relat_1 @ X1)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['6', '7'])).
% 1.13/1.34  thf('9', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.13/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.13/1.34  thf('10', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (~ (v1_relat_1 @ X0)
% 1.13/1.34          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 1.13/1.34          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.34  thf('11', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (~ (v1_xboole_0 @ X0)
% 1.13/1.34          | ~ (v1_funct_1 @ X0)
% 1.13/1.34          | ~ (v1_relat_1 @ X0)
% 1.13/1.34          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 1.13/1.34          | ~ (v1_relat_1 @ X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['5', '10'])).
% 1.13/1.34  thf('12', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 1.13/1.34          | ~ (v1_relat_1 @ X0)
% 1.13/1.34          | ~ (v1_funct_1 @ X0)
% 1.13/1.34          | ~ (v1_xboole_0 @ X0))),
% 1.13/1.34      inference('simplify', [status(thm)], ['11'])).
% 1.13/1.34  thf(t116_funct_2, conjecture,
% 1.13/1.34    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.34     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.13/1.34         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.13/1.34       ( ![E:$i]:
% 1.13/1.34         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.13/1.34              ( ![F:$i]:
% 1.13/1.34                ( ( m1_subset_1 @ F @ A ) =>
% 1.13/1.34                  ( ~( ( r2_hidden @ F @ C ) & 
% 1.13/1.34                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 1.13/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.34    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.34        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.13/1.34            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.13/1.34          ( ![E:$i]:
% 1.13/1.34            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.13/1.34                 ( ![F:$i]:
% 1.13/1.34                   ( ( m1_subset_1 @ F @ A ) =>
% 1.13/1.34                     ( ~( ( r2_hidden @ F @ C ) & 
% 1.13/1.34                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 1.13/1.34    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 1.13/1.34  thf('13', plain,
% 1.13/1.34      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('14', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.13/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.13/1.34  thf('15', plain,
% 1.13/1.34      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['13', '14'])).
% 1.13/1.34  thf('16', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf(redefinition_k7_relset_1, axiom,
% 1.13/1.34    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.34       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.13/1.34  thf('17', plain,
% 1.13/1.34      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.13/1.34         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.13/1.34          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 1.13/1.34      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.13/1.34  thf('18', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 1.13/1.34           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['16', '17'])).
% 1.13/1.34  thf('19', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 1.13/1.34      inference('demod', [status(thm)], ['15', '18'])).
% 1.13/1.34  thf('20', plain,
% 1.13/1.34      ((~ (v1_xboole_0 @ sk_D_1)
% 1.13/1.34        | ~ (v1_funct_1 @ sk_D_1)
% 1.13/1.34        | ~ (v1_relat_1 @ sk_D_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['12', '19'])).
% 1.13/1.34  thf('21', plain, ((v1_funct_1 @ sk_D_1)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('22', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf(cc2_relat_1, axiom,
% 1.13/1.34    (![A:$i]:
% 1.13/1.34     ( ( v1_relat_1 @ A ) =>
% 1.13/1.34       ( ![B:$i]:
% 1.13/1.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.13/1.34  thf('23', plain,
% 1.13/1.34      (![X12 : $i, X13 : $i]:
% 1.13/1.34         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 1.13/1.34          | (v1_relat_1 @ X12)
% 1.13/1.34          | ~ (v1_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.13/1.34  thf('24', plain,
% 1.13/1.34      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['22', '23'])).
% 1.13/1.34  thf(fc6_relat_1, axiom,
% 1.13/1.34    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.13/1.34  thf('25', plain,
% 1.13/1.34      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 1.13/1.34      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.13/1.34  thf('26', plain, ((v1_relat_1 @ sk_D_1)),
% 1.13/1.34      inference('demod', [status(thm)], ['24', '25'])).
% 1.13/1.34  thf('27', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 1.13/1.34      inference('demod', [status(thm)], ['20', '21', '26'])).
% 1.13/1.34  thf('28', plain,
% 1.13/1.34      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('29', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 1.13/1.34           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['16', '17'])).
% 1.13/1.34  thf('30', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 1.13/1.34      inference('demod', [status(thm)], ['28', '29'])).
% 1.13/1.34  thf('31', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf(t52_relset_1, axiom,
% 1.13/1.34    (![A:$i]:
% 1.13/1.34     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.13/1.34       ( ![B:$i]:
% 1.13/1.34         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.13/1.34           ( ![C:$i]:
% 1.13/1.34             ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.13/1.34               ( ![D:$i]:
% 1.13/1.34                 ( ( m1_subset_1 @
% 1.13/1.34                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.13/1.34                   ( ![E:$i]:
% 1.13/1.34                     ( ( m1_subset_1 @ E @ A ) =>
% 1.13/1.34                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 1.13/1.34                         ( ?[F:$i]:
% 1.13/1.34                           ( ( r2_hidden @ F @ B ) & 
% 1.13/1.34                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 1.13/1.34                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.13/1.34  thf('32', plain,
% 1.13/1.34      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X46 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ X41)
% 1.13/1.34          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.13/1.34          | ~ (r2_hidden @ X46 @ (k7_relset_1 @ X43 @ X44 @ X42 @ X41))
% 1.13/1.34          | (r2_hidden @ (k4_tarski @ (sk_F @ X46 @ X42 @ X43 @ X41) @ X46) @ 
% 1.13/1.34             X42)
% 1.13/1.34          | ~ (m1_subset_1 @ X46 @ X44)
% 1.13/1.34          | (v1_xboole_0 @ X43)
% 1.13/1.34          | (v1_xboole_0 @ X44))),
% 1.13/1.34      inference('cnf', [status(esa)], [t52_relset_1])).
% 1.13/1.34  thf('33', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ sk_B_1)
% 1.13/1.34          | (v1_xboole_0 @ sk_A)
% 1.13/1.34          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.13/1.34          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 1.13/1.34             sk_D_1)
% 1.13/1.34          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 1.13/1.34          | (v1_xboole_0 @ X1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['31', '32'])).
% 1.13/1.34  thf('34', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 1.13/1.34           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['16', '17'])).
% 1.13/1.34  thf('35', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ sk_B_1)
% 1.13/1.34          | (v1_xboole_0 @ sk_A)
% 1.13/1.34          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.13/1.34          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 1.13/1.34             sk_D_1)
% 1.13/1.34          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 1.13/1.34          | (v1_xboole_0 @ X1))),
% 1.13/1.34      inference('demod', [status(thm)], ['33', '34'])).
% 1.13/1.34  thf('36', plain,
% 1.13/1.34      (((v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | (r2_hidden @ 
% 1.13/1.34           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_E) @ sk_D_1)
% 1.13/1.34        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_B_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['30', '35'])).
% 1.13/1.34  thf('37', plain,
% 1.13/1.34      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('38', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf(dt_k7_relset_1, axiom,
% 1.13/1.34    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.34       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.13/1.34  thf('39', plain,
% 1.13/1.34      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.13/1.34         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.13/1.34          | (m1_subset_1 @ (k7_relset_1 @ X30 @ X31 @ X29 @ X32) @ 
% 1.13/1.34             (k1_zfmisc_1 @ X31)))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 1.13/1.34  thf('40', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ 
% 1.13/1.34          (k1_zfmisc_1 @ sk_B_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['38', '39'])).
% 1.13/1.34  thf(t4_subset, axiom,
% 1.13/1.34    (![A:$i,B:$i,C:$i]:
% 1.13/1.34     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.13/1.34       ( m1_subset_1 @ A @ C ) ))).
% 1.13/1.34  thf('41', plain,
% 1.13/1.34      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.13/1.34         (~ (r2_hidden @ X9 @ X10)
% 1.13/1.34          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.13/1.34          | (m1_subset_1 @ X9 @ X11))),
% 1.13/1.34      inference('cnf', [status(esa)], [t4_subset])).
% 1.13/1.34  thf('42', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((m1_subset_1 @ X1 @ sk_B_1)
% 1.13/1.34          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['40', '41'])).
% 1.13/1.34  thf('43', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 1.13/1.34      inference('sup-', [status(thm)], ['37', '42'])).
% 1.13/1.34  thf('44', plain,
% 1.13/1.34      (((v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | (r2_hidden @ 
% 1.13/1.34           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_E) @ sk_D_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_B_1))),
% 1.13/1.34      inference('demod', [status(thm)], ['36', '43'])).
% 1.13/1.34  thf('45', plain,
% 1.13/1.34      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.13/1.34         (~ (r2_hidden @ (k4_tarski @ X20 @ X22) @ X21)
% 1.13/1.34          | ((X22) = (k1_funct_1 @ X21 @ X20))
% 1.13/1.34          | ~ (v1_funct_1 @ X21)
% 1.13/1.34          | ~ (v1_relat_1 @ X21))),
% 1.13/1.34      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.13/1.34  thf('46', plain,
% 1.13/1.34      (((v1_xboole_0 @ sk_B_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | ~ (v1_relat_1 @ sk_D_1)
% 1.13/1.34        | ~ (v1_funct_1 @ sk_D_1)
% 1.13/1.34        | ((sk_E)
% 1.13/1.34            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 1.13/1.34      inference('sup-', [status(thm)], ['44', '45'])).
% 1.13/1.34  thf('47', plain, ((v1_relat_1 @ sk_D_1)),
% 1.13/1.34      inference('demod', [status(thm)], ['24', '25'])).
% 1.13/1.34  thf('48', plain, ((v1_funct_1 @ sk_D_1)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('49', plain,
% 1.13/1.34      (((v1_xboole_0 @ sk_B_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | ((sk_E)
% 1.13/1.34            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 1.13/1.34      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.13/1.34  thf('50', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 1.13/1.34      inference('demod', [status(thm)], ['28', '29'])).
% 1.13/1.34  thf('51', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('52', plain,
% 1.13/1.34      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X46 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ X41)
% 1.13/1.34          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.13/1.34          | ~ (r2_hidden @ X46 @ (k7_relset_1 @ X43 @ X44 @ X42 @ X41))
% 1.13/1.34          | (m1_subset_1 @ (sk_F @ X46 @ X42 @ X43 @ X41) @ X43)
% 1.13/1.34          | ~ (m1_subset_1 @ X46 @ X44)
% 1.13/1.34          | (v1_xboole_0 @ X43)
% 1.13/1.34          | (v1_xboole_0 @ X44))),
% 1.13/1.34      inference('cnf', [status(esa)], [t52_relset_1])).
% 1.13/1.34  thf('53', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ sk_B_1)
% 1.13/1.34          | (v1_xboole_0 @ sk_A)
% 1.13/1.34          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.13/1.34          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 1.13/1.34          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 1.13/1.34          | (v1_xboole_0 @ X1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['51', '52'])).
% 1.13/1.34  thf('54', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 1.13/1.34           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['16', '17'])).
% 1.13/1.34  thf('55', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ sk_B_1)
% 1.13/1.34          | (v1_xboole_0 @ sk_A)
% 1.13/1.34          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.13/1.34          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 1.13/1.34          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 1.13/1.34          | (v1_xboole_0 @ X1))),
% 1.13/1.34      inference('demod', [status(thm)], ['53', '54'])).
% 1.13/1.34  thf('56', plain,
% 1.13/1.34      (((v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.13/1.34        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_B_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['50', '55'])).
% 1.13/1.34  thf('57', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 1.13/1.34      inference('sup-', [status(thm)], ['37', '42'])).
% 1.13/1.34  thf('58', plain,
% 1.13/1.34      (((v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_B_1))),
% 1.13/1.34      inference('demod', [status(thm)], ['56', '57'])).
% 1.13/1.34  thf('59', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 1.13/1.34      inference('demod', [status(thm)], ['28', '29'])).
% 1.13/1.34  thf('60', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('61', plain,
% 1.13/1.34      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X46 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ X41)
% 1.13/1.34          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.13/1.34          | ~ (r2_hidden @ X46 @ (k7_relset_1 @ X43 @ X44 @ X42 @ X41))
% 1.13/1.34          | (r2_hidden @ (sk_F @ X46 @ X42 @ X43 @ X41) @ X41)
% 1.13/1.34          | ~ (m1_subset_1 @ X46 @ X44)
% 1.13/1.34          | (v1_xboole_0 @ X43)
% 1.13/1.34          | (v1_xboole_0 @ X44))),
% 1.13/1.34      inference('cnf', [status(esa)], [t52_relset_1])).
% 1.13/1.34  thf('62', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ sk_B_1)
% 1.13/1.34          | (v1_xboole_0 @ sk_A)
% 1.13/1.34          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.13/1.34          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 1.13/1.34          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 1.13/1.34          | (v1_xboole_0 @ X1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['60', '61'])).
% 1.13/1.34  thf('63', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 1.13/1.34           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['16', '17'])).
% 1.13/1.34  thf('64', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ sk_B_1)
% 1.13/1.34          | (v1_xboole_0 @ sk_A)
% 1.13/1.34          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.13/1.34          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 1.13/1.34          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 1.13/1.34          | (v1_xboole_0 @ X1))),
% 1.13/1.34      inference('demod', [status(thm)], ['62', '63'])).
% 1.13/1.34  thf('65', plain,
% 1.13/1.34      (((v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 1.13/1.34        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_B_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['59', '64'])).
% 1.13/1.34  thf('66', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 1.13/1.34      inference('sup-', [status(thm)], ['37', '42'])).
% 1.13/1.34  thf('67', plain,
% 1.13/1.34      (((v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_B_1))),
% 1.13/1.34      inference('demod', [status(thm)], ['65', '66'])).
% 1.13/1.34  thf('68', plain,
% 1.13/1.34      (![X47 : $i]:
% 1.13/1.34         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X47))
% 1.13/1.34          | ~ (r2_hidden @ X47 @ sk_C_1)
% 1.13/1.34          | ~ (m1_subset_1 @ X47 @ sk_A))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('69', plain,
% 1.13/1.34      (((v1_xboole_0 @ sk_B_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | ~ (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.13/1.34        | ((sk_E)
% 1.13/1.34            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 1.13/1.34      inference('sup-', [status(thm)], ['67', '68'])).
% 1.13/1.34  thf('70', plain,
% 1.13/1.34      (((v1_xboole_0 @ sk_B_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | ((sk_E)
% 1.13/1.34            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1)))
% 1.13/1.34        | (v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_B_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['58', '69'])).
% 1.13/1.34  thf('71', plain,
% 1.13/1.34      ((((sk_E)
% 1.13/1.34          != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1)))
% 1.13/1.34        | (v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_B_1))),
% 1.13/1.34      inference('simplify', [status(thm)], ['70'])).
% 1.13/1.34  thf('72', plain,
% 1.13/1.34      ((((sk_E) != (sk_E))
% 1.13/1.34        | (v1_xboole_0 @ sk_C_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_B_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_B_1)
% 1.13/1.34        | (v1_xboole_0 @ sk_A)
% 1.13/1.34        | (v1_xboole_0 @ sk_C_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['49', '71'])).
% 1.13/1.34  thf('73', plain,
% 1.13/1.34      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 1.13/1.34      inference('simplify', [status(thm)], ['72'])).
% 1.13/1.34  thf('74', plain,
% 1.13/1.34      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.13/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.13/1.34  thf('75', plain,
% 1.13/1.34      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.13/1.34         (~ (r2_hidden @ X18 @ (k9_relat_1 @ X19 @ X17))
% 1.13/1.34          | (r2_hidden @ (sk_D @ X19 @ X17 @ X18) @ X17)
% 1.13/1.34          | ~ (v1_relat_1 @ X19))),
% 1.13/1.34      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.13/1.34  thf('76', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 1.13/1.34          | ~ (v1_relat_1 @ X1)
% 1.13/1.34          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 1.13/1.34             X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['74', '75'])).
% 1.13/1.34  thf('77', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.13/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.13/1.34  thf('78', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (~ (v1_relat_1 @ X1)
% 1.13/1.34          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 1.13/1.34          | ~ (v1_xboole_0 @ X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['76', '77'])).
% 1.13/1.34  thf('79', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 1.13/1.34      inference('demod', [status(thm)], ['15', '18'])).
% 1.13/1.34  thf('80', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_relat_1 @ sk_D_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['78', '79'])).
% 1.13/1.34  thf('81', plain, ((v1_relat_1 @ sk_D_1)),
% 1.13/1.34      inference('demod', [status(thm)], ['24', '25'])).
% 1.13/1.34  thf('82', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.13/1.34      inference('demod', [status(thm)], ['80', '81'])).
% 1.13/1.34  thf('83', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 1.13/1.34      inference('clc', [status(thm)], ['73', '82'])).
% 1.13/1.34  thf('84', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf(cc4_relset_1, axiom,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( v1_xboole_0 @ A ) =>
% 1.13/1.34       ( ![C:$i]:
% 1.13/1.34         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.13/1.34           ( v1_xboole_0 @ C ) ) ) ))).
% 1.13/1.34  thf('85', plain,
% 1.13/1.34      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.13/1.34         (~ (v1_xboole_0 @ X26)
% 1.13/1.34          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 1.13/1.34          | (v1_xboole_0 @ X27))),
% 1.13/1.34      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.13/1.34  thf('86', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['84', '85'])).
% 1.13/1.34  thf('87', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['83', '86'])).
% 1.13/1.34  thf('88', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf(cc3_relset_1, axiom,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( v1_xboole_0 @ A ) =>
% 1.13/1.34       ( ![C:$i]:
% 1.13/1.34         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.34           ( v1_xboole_0 @ C ) ) ) ))).
% 1.13/1.34  thf('89', plain,
% 1.13/1.34      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.13/1.34         (~ (v1_xboole_0 @ X23)
% 1.13/1.34          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X25)))
% 1.13/1.34          | (v1_xboole_0 @ X24))),
% 1.13/1.34      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.13/1.34  thf('90', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_A))),
% 1.13/1.34      inference('sup-', [status(thm)], ['88', '89'])).
% 1.13/1.34  thf('91', plain, ((v1_xboole_0 @ sk_D_1)),
% 1.13/1.34      inference('clc', [status(thm)], ['87', '90'])).
% 1.13/1.34  thf('92', plain, ($false), inference('demod', [status(thm)], ['27', '91'])).
% 1.13/1.34  
% 1.13/1.34  % SZS output end Refutation
% 1.13/1.34  
% 1.13/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
