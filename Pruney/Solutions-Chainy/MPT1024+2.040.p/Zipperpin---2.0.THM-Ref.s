%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bTu2SmrphY

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:39 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 257 expanded)
%              Number of leaves         :   34 (  89 expanded)
%              Depth                    :   17
%              Number of atoms          : 1189 (3608 expanded)
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

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

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
      | ( r2_hidden @ ( sk_F @ X46 @ X42 @ X43 @ X41 ) @ X41 )
      | ~ ( m1_subset_1 @ X46 @ X44 )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
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
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','42'])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
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
      | ( m1_subset_1 @ ( sk_F @ X46 @ X42 @ X43 @ X41 ) @ X43 )
      | ~ ( m1_subset_1 @ X46 @ X44 )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
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
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','42'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X47: $i] :
      ( ~ ( r2_hidden @ X47 @ sk_A )
      | ~ ( r2_hidden @ X47 @ sk_C_1 )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','72'])).

thf('74',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('78',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k9_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( sk_D @ X19 @ X17 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['76','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('88',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('92',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X25 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('93',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['90','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['27','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bTu2SmrphY
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:12:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.06/1.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.24  % Solved by: fo/fo7.sh
% 1.06/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.24  % done 992 iterations in 0.769s
% 1.06/1.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.24  % SZS output start Refutation
% 1.06/1.24  thf(sk_B_type, type, sk_B: $i > $i).
% 1.06/1.24  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.06/1.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.24  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 1.06/1.24  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.06/1.24  thf(sk_E_type, type, sk_E: $i).
% 1.06/1.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.24  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.06/1.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.06/1.24  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.06/1.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.06/1.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.06/1.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.24  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.06/1.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.06/1.24  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.06/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.24  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.06/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.24  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.06/1.24  thf(d1_xboole_0, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.06/1.24  thf('0', plain,
% 1.06/1.24      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf(t8_funct_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i]:
% 1.06/1.24     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.06/1.24       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.06/1.24         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.06/1.24           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.06/1.24  thf('1', plain,
% 1.06/1.24      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.06/1.24         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 1.06/1.24          | ((X22) != (k1_funct_1 @ X21 @ X20))
% 1.06/1.24          | (r2_hidden @ (k4_tarski @ X20 @ X22) @ X21)
% 1.06/1.24          | ~ (v1_funct_1 @ X21)
% 1.06/1.24          | ~ (v1_relat_1 @ X21))),
% 1.06/1.24      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.06/1.24  thf('2', plain,
% 1.06/1.24      (![X20 : $i, X21 : $i]:
% 1.06/1.24         (~ (v1_relat_1 @ X21)
% 1.06/1.24          | ~ (v1_funct_1 @ X21)
% 1.06/1.24          | (r2_hidden @ (k4_tarski @ X20 @ (k1_funct_1 @ X21 @ X20)) @ X21)
% 1.06/1.24          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X21)))),
% 1.06/1.24      inference('simplify', [status(thm)], ['1'])).
% 1.06/1.24  thf('3', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.06/1.24          | (r2_hidden @ 
% 1.06/1.24             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 1.06/1.24              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 1.06/1.24             X0)
% 1.06/1.24          | ~ (v1_funct_1 @ X0)
% 1.06/1.24          | ~ (v1_relat_1 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['0', '2'])).
% 1.06/1.24  thf('4', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf('5', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (~ (v1_relat_1 @ X0)
% 1.06/1.24          | ~ (v1_funct_1 @ X0)
% 1.06/1.24          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.06/1.24          | ~ (v1_xboole_0 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['3', '4'])).
% 1.06/1.24  thf('6', plain,
% 1.06/1.24      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf(t143_relat_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i]:
% 1.06/1.24     ( ( v1_relat_1 @ C ) =>
% 1.06/1.24       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.06/1.24         ( ?[D:$i]:
% 1.06/1.24           ( ( r2_hidden @ D @ B ) & 
% 1.06/1.24             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.06/1.24             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.06/1.24  thf('7', plain,
% 1.06/1.24      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.06/1.24         (~ (r2_hidden @ X18 @ (k9_relat_1 @ X19 @ X17))
% 1.06/1.24          | (r2_hidden @ (sk_D @ X19 @ X17 @ X18) @ (k1_relat_1 @ X19))
% 1.06/1.24          | ~ (v1_relat_1 @ X19))),
% 1.06/1.24      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.06/1.24  thf('8', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 1.06/1.24          | ~ (v1_relat_1 @ X1)
% 1.06/1.24          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 1.06/1.24             (k1_relat_1 @ X1)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['6', '7'])).
% 1.06/1.24  thf('9', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf('10', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (~ (v1_relat_1 @ X0)
% 1.06/1.24          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 1.06/1.24          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['8', '9'])).
% 1.06/1.24  thf('11', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (~ (v1_xboole_0 @ X0)
% 1.06/1.24          | ~ (v1_funct_1 @ X0)
% 1.06/1.24          | ~ (v1_relat_1 @ X0)
% 1.06/1.24          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 1.06/1.24          | ~ (v1_relat_1 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['5', '10'])).
% 1.06/1.24  thf('12', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 1.06/1.24          | ~ (v1_relat_1 @ X0)
% 1.06/1.24          | ~ (v1_funct_1 @ X0)
% 1.06/1.24          | ~ (v1_xboole_0 @ X0))),
% 1.06/1.24      inference('simplify', [status(thm)], ['11'])).
% 1.06/1.24  thf(t115_funct_2, conjecture,
% 1.06/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.24     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.06/1.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.24       ( ![E:$i]:
% 1.06/1.24         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.06/1.24              ( ![F:$i]:
% 1.06/1.24                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 1.06/1.24                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 1.06/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.24    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.24        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.06/1.24            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.24          ( ![E:$i]:
% 1.06/1.24            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.06/1.24                 ( ![F:$i]:
% 1.06/1.24                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 1.06/1.24                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 1.06/1.24    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 1.06/1.24  thf('13', plain,
% 1.06/1.24      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('14', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf('15', plain,
% 1.06/1.24      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['13', '14'])).
% 1.06/1.24  thf('16', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(redefinition_k7_relset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.24       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.06/1.24  thf('17', plain,
% 1.06/1.24      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.06/1.24          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 1.06/1.24      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.06/1.24  thf('18', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 1.06/1.24           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.24  thf('19', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 1.06/1.24      inference('demod', [status(thm)], ['15', '18'])).
% 1.06/1.24  thf('20', plain,
% 1.06/1.24      ((~ (v1_xboole_0 @ sk_D_1)
% 1.06/1.24        | ~ (v1_funct_1 @ sk_D_1)
% 1.06/1.24        | ~ (v1_relat_1 @ sk_D_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['12', '19'])).
% 1.06/1.24  thf('21', plain, ((v1_funct_1 @ sk_D_1)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('22', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(cc2_relat_1, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( v1_relat_1 @ A ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.06/1.24  thf('23', plain,
% 1.06/1.24      (![X12 : $i, X13 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 1.06/1.24          | (v1_relat_1 @ X12)
% 1.06/1.24          | ~ (v1_relat_1 @ X13))),
% 1.06/1.24      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.06/1.24  thf('24', plain,
% 1.06/1.24      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['22', '23'])).
% 1.06/1.24  thf(fc6_relat_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.06/1.24  thf('25', plain,
% 1.06/1.24      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 1.06/1.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.06/1.24  thf('26', plain, ((v1_relat_1 @ sk_D_1)),
% 1.06/1.24      inference('demod', [status(thm)], ['24', '25'])).
% 1.06/1.24  thf('27', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 1.06/1.24      inference('demod', [status(thm)], ['20', '21', '26'])).
% 1.06/1.24  thf('28', plain,
% 1.06/1.24      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('29', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 1.06/1.24           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.24  thf('30', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 1.06/1.24      inference('demod', [status(thm)], ['28', '29'])).
% 1.06/1.24  thf('31', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(t52_relset_1, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.06/1.24           ( ![C:$i]:
% 1.06/1.24             ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.06/1.24               ( ![D:$i]:
% 1.06/1.24                 ( ( m1_subset_1 @
% 1.06/1.24                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.06/1.24                   ( ![E:$i]:
% 1.06/1.24                     ( ( m1_subset_1 @ E @ A ) =>
% 1.06/1.24                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 1.06/1.24                         ( ?[F:$i]:
% 1.06/1.24                           ( ( r2_hidden @ F @ B ) & 
% 1.06/1.24                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 1.06/1.24                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.24  thf('32', plain,
% 1.06/1.24      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X46 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ X41)
% 1.06/1.24          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.06/1.24          | ~ (r2_hidden @ X46 @ (k7_relset_1 @ X43 @ X44 @ X42 @ X41))
% 1.06/1.24          | (r2_hidden @ (k4_tarski @ (sk_F @ X46 @ X42 @ X43 @ X41) @ X46) @ 
% 1.06/1.24             X42)
% 1.06/1.24          | ~ (m1_subset_1 @ X46 @ X44)
% 1.06/1.24          | (v1_xboole_0 @ X43)
% 1.06/1.24          | (v1_xboole_0 @ X44))),
% 1.06/1.24      inference('cnf', [status(esa)], [t52_relset_1])).
% 1.06/1.24  thf('33', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ sk_B_1)
% 1.06/1.24          | (v1_xboole_0 @ sk_A)
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.06/1.24          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 1.06/1.24             sk_D_1)
% 1.06/1.24          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 1.06/1.24          | (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['31', '32'])).
% 1.06/1.24  thf('34', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 1.06/1.24           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.24  thf('35', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ sk_B_1)
% 1.06/1.24          | (v1_xboole_0 @ sk_A)
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.06/1.24          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 1.06/1.24             sk_D_1)
% 1.06/1.24          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 1.06/1.24          | (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('demod', [status(thm)], ['33', '34'])).
% 1.06/1.24  thf('36', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | (r2_hidden @ 
% 1.06/1.24           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_E) @ sk_D_1)
% 1.06/1.24        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['30', '35'])).
% 1.06/1.24  thf('37', plain,
% 1.06/1.24      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('38', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(dt_k7_relset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.24       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.06/1.24  thf('39', plain,
% 1.06/1.24      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.06/1.24          | (m1_subset_1 @ (k7_relset_1 @ X30 @ X31 @ X29 @ X32) @ 
% 1.06/1.24             (k1_zfmisc_1 @ X31)))),
% 1.06/1.24      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 1.06/1.24  thf('40', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ 
% 1.06/1.24          (k1_zfmisc_1 @ sk_B_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['38', '39'])).
% 1.06/1.24  thf(t4_subset, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i]:
% 1.06/1.24     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.06/1.24       ( m1_subset_1 @ A @ C ) ))).
% 1.06/1.24  thf('41', plain,
% 1.06/1.24      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.06/1.24         (~ (r2_hidden @ X9 @ X10)
% 1.06/1.24          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.06/1.24          | (m1_subset_1 @ X9 @ X11))),
% 1.06/1.24      inference('cnf', [status(esa)], [t4_subset])).
% 1.06/1.24  thf('42', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((m1_subset_1 @ X1 @ sk_B_1)
% 1.06/1.24          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['40', '41'])).
% 1.06/1.24  thf('43', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 1.06/1.24      inference('sup-', [status(thm)], ['37', '42'])).
% 1.06/1.24  thf('44', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | (r2_hidden @ 
% 1.06/1.24           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_E) @ sk_D_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.24      inference('demod', [status(thm)], ['36', '43'])).
% 1.06/1.24  thf('45', plain,
% 1.06/1.24      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.06/1.24         (~ (r2_hidden @ (k4_tarski @ X20 @ X22) @ X21)
% 1.06/1.24          | ((X22) = (k1_funct_1 @ X21 @ X20))
% 1.06/1.24          | ~ (v1_funct_1 @ X21)
% 1.06/1.24          | ~ (v1_relat_1 @ X21))),
% 1.06/1.24      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.06/1.24  thf('46', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_B_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | ~ (v1_relat_1 @ sk_D_1)
% 1.06/1.24        | ~ (v1_funct_1 @ sk_D_1)
% 1.06/1.24        | ((sk_E)
% 1.06/1.24            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['44', '45'])).
% 1.06/1.24  thf('47', plain, ((v1_relat_1 @ sk_D_1)),
% 1.06/1.24      inference('demod', [status(thm)], ['24', '25'])).
% 1.06/1.24  thf('48', plain, ((v1_funct_1 @ sk_D_1)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('49', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_B_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | ((sk_E)
% 1.06/1.24            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 1.06/1.24      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.06/1.24  thf('50', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 1.06/1.24      inference('demod', [status(thm)], ['28', '29'])).
% 1.06/1.24  thf('51', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('52', plain,
% 1.06/1.24      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X46 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ X41)
% 1.06/1.24          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.06/1.24          | ~ (r2_hidden @ X46 @ (k7_relset_1 @ X43 @ X44 @ X42 @ X41))
% 1.06/1.24          | (r2_hidden @ (sk_F @ X46 @ X42 @ X43 @ X41) @ X41)
% 1.06/1.24          | ~ (m1_subset_1 @ X46 @ X44)
% 1.06/1.24          | (v1_xboole_0 @ X43)
% 1.06/1.24          | (v1_xboole_0 @ X44))),
% 1.06/1.24      inference('cnf', [status(esa)], [t52_relset_1])).
% 1.06/1.24  thf('53', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ sk_B_1)
% 1.06/1.24          | (v1_xboole_0 @ sk_A)
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.06/1.24          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 1.06/1.24          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 1.06/1.24          | (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['51', '52'])).
% 1.06/1.24  thf('54', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 1.06/1.24           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.24  thf('55', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ sk_B_1)
% 1.06/1.24          | (v1_xboole_0 @ sk_A)
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.06/1.24          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 1.06/1.24          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 1.06/1.24          | (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('demod', [status(thm)], ['53', '54'])).
% 1.06/1.24  thf('56', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 1.06/1.24        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['50', '55'])).
% 1.06/1.24  thf('57', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 1.06/1.24      inference('sup-', [status(thm)], ['37', '42'])).
% 1.06/1.24  thf('58', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.24      inference('demod', [status(thm)], ['56', '57'])).
% 1.06/1.24  thf('59', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 1.06/1.24      inference('demod', [status(thm)], ['28', '29'])).
% 1.06/1.24  thf('60', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('61', plain,
% 1.06/1.24      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X46 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ X41)
% 1.06/1.24          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.06/1.24          | ~ (r2_hidden @ X46 @ (k7_relset_1 @ X43 @ X44 @ X42 @ X41))
% 1.06/1.24          | (m1_subset_1 @ (sk_F @ X46 @ X42 @ X43 @ X41) @ X43)
% 1.06/1.24          | ~ (m1_subset_1 @ X46 @ X44)
% 1.06/1.24          | (v1_xboole_0 @ X43)
% 1.06/1.24          | (v1_xboole_0 @ X44))),
% 1.06/1.24      inference('cnf', [status(esa)], [t52_relset_1])).
% 1.06/1.24  thf('62', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ sk_B_1)
% 1.06/1.24          | (v1_xboole_0 @ sk_A)
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.06/1.24          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 1.06/1.24          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 1.06/1.24          | (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.24  thf('63', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 1.06/1.24           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.24  thf('64', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ sk_B_1)
% 1.06/1.24          | (v1_xboole_0 @ sk_A)
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.06/1.24          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 1.06/1.24          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 1.06/1.24          | (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('demod', [status(thm)], ['62', '63'])).
% 1.06/1.24  thf('65', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.06/1.24        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['59', '64'])).
% 1.06/1.24  thf('66', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 1.06/1.24      inference('sup-', [status(thm)], ['37', '42'])).
% 1.06/1.24  thf('67', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.24      inference('demod', [status(thm)], ['65', '66'])).
% 1.06/1.24  thf(t2_subset, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ A @ B ) =>
% 1.06/1.24       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.06/1.24  thf('68', plain,
% 1.06/1.24      (![X7 : $i, X8 : $i]:
% 1.06/1.24         ((r2_hidden @ X7 @ X8)
% 1.06/1.24          | (v1_xboole_0 @ X8)
% 1.06/1.24          | ~ (m1_subset_1 @ X7 @ X8))),
% 1.06/1.24      inference('cnf', [status(esa)], [t2_subset])).
% 1.06/1.24  thf('69', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_B_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['67', '68'])).
% 1.06/1.24  thf('70', plain,
% 1.06/1.24      (((r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.24      inference('simplify', [status(thm)], ['69'])).
% 1.06/1.24  thf('71', plain,
% 1.06/1.24      (![X47 : $i]:
% 1.06/1.24         (~ (r2_hidden @ X47 @ sk_A)
% 1.06/1.24          | ~ (r2_hidden @ X47 @ sk_C_1)
% 1.06/1.24          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X47)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('72', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_B_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | ((sk_E)
% 1.06/1.24            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1)))
% 1.06/1.24        | ~ (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['70', '71'])).
% 1.06/1.24  thf('73', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_B_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | ((sk_E)
% 1.06/1.24            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1)))
% 1.06/1.24        | (v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['58', '72'])).
% 1.06/1.24  thf('74', plain,
% 1.06/1.24      ((((sk_E)
% 1.06/1.24          != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1)))
% 1.06/1.24        | (v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.24      inference('simplify', [status(thm)], ['73'])).
% 1.06/1.24  thf('75', plain,
% 1.06/1.24      ((((sk_E) != (sk_E))
% 1.06/1.24        | (v1_xboole_0 @ sk_C_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_B_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_B_1)
% 1.06/1.24        | (v1_xboole_0 @ sk_A)
% 1.06/1.24        | (v1_xboole_0 @ sk_C_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['49', '74'])).
% 1.06/1.24  thf('76', plain,
% 1.06/1.24      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 1.06/1.24      inference('simplify', [status(thm)], ['75'])).
% 1.06/1.24  thf('77', plain,
% 1.06/1.24      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf('78', plain,
% 1.06/1.24      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.06/1.24         (~ (r2_hidden @ X18 @ (k9_relat_1 @ X19 @ X17))
% 1.06/1.24          | (r2_hidden @ (sk_D @ X19 @ X17 @ X18) @ X17)
% 1.06/1.24          | ~ (v1_relat_1 @ X19))),
% 1.06/1.24      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.06/1.24  thf('79', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 1.06/1.24          | ~ (v1_relat_1 @ X1)
% 1.06/1.24          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 1.06/1.24             X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['77', '78'])).
% 1.06/1.24  thf('80', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf('81', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (~ (v1_relat_1 @ X1)
% 1.06/1.24          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 1.06/1.24          | ~ (v1_xboole_0 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['79', '80'])).
% 1.06/1.24  thf('82', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 1.06/1.24      inference('demod', [status(thm)], ['15', '18'])).
% 1.06/1.24  thf('83', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_relat_1 @ sk_D_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['81', '82'])).
% 1.06/1.24  thf('84', plain, ((v1_relat_1 @ sk_D_1)),
% 1.06/1.24      inference('demod', [status(thm)], ['24', '25'])).
% 1.06/1.24  thf('85', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.06/1.24      inference('demod', [status(thm)], ['83', '84'])).
% 1.06/1.24  thf('86', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.24      inference('clc', [status(thm)], ['76', '85'])).
% 1.06/1.24  thf('87', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(cc4_relset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( v1_xboole_0 @ A ) =>
% 1.06/1.24       ( ![C:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.06/1.24           ( v1_xboole_0 @ C ) ) ) ))).
% 1.06/1.24  thf('88', plain,
% 1.06/1.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.06/1.24         (~ (v1_xboole_0 @ X26)
% 1.06/1.24          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 1.06/1.24          | (v1_xboole_0 @ X27))),
% 1.06/1.24      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.06/1.24  thf('89', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['87', '88'])).
% 1.06/1.24  thf('90', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['86', '89'])).
% 1.06/1.24  thf('91', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(cc3_relset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( v1_xboole_0 @ A ) =>
% 1.06/1.24       ( ![C:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.24           ( v1_xboole_0 @ C ) ) ) ))).
% 1.06/1.24  thf('92', plain,
% 1.06/1.24      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.24         (~ (v1_xboole_0 @ X23)
% 1.06/1.24          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X25)))
% 1.06/1.24          | (v1_xboole_0 @ X24))),
% 1.06/1.24      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.06/1.24  thf('93', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['91', '92'])).
% 1.06/1.24  thf('94', plain, ((v1_xboole_0 @ sk_D_1)),
% 1.06/1.24      inference('clc', [status(thm)], ['90', '93'])).
% 1.06/1.24  thf('95', plain, ($false), inference('demod', [status(thm)], ['27', '94'])).
% 1.06/1.24  
% 1.06/1.24  % SZS output end Refutation
% 1.06/1.24  
% 1.06/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
