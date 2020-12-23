%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MFD0lUMzW7

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:36 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 248 expanded)
%              Number of leaves         :   33 (  86 expanded)
%              Depth                    :   17
%              Number of atoms          : 1182 (3573 expanded)
%              Number of equality atoms :   19 (  95 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( X17
       != ( k1_funct_1 @ X16 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( k1_funct_1 @ X16 @ X15 ) ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['20','21','24'])).

thf('26',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('28',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_hidden @ X40 @ ( k7_relset_1 @ X37 @ X38 @ X36 @ X35 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X40 @ X36 @ X37 @ X35 ) @ X40 ) @ X36 )
      | ~ ( m1_subset_1 @ X40 @ X38 )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_E ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_E ) @ sk_D_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( X17
        = ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('46',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('49',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_hidden @ X40 @ ( k7_relset_1 @ X37 @ X38 @ X36 @ X35 ) )
      | ( r2_hidden @ ( sk_F @ X40 @ X36 @ X37 @ X35 ) @ X35 )
      | ~ ( m1_subset_1 @ X40 @ X38 )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['35','40'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('58',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_hidden @ X40 @ ( k7_relset_1 @ X37 @ X38 @ X36 @ X35 ) )
      | ( m1_subset_1 @ ( sk_F @ X40 @ X36 @ X37 @ X35 ) @ X37 )
      | ~ ( m1_subset_1 @ X40 @ X38 )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['35','40'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('66',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_A )
      | ~ ( r2_hidden @ X41 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ~ ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf('72',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('76',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['74','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('86',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('90',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X23 ) ) )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['88','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['25','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MFD0lUMzW7
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 297 iterations in 0.182s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.63  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.63  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.45/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(d1_xboole_0, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.63  thf(t8_funct_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.63       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.45/0.63         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.45/0.63           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.45/0.63          | ((X17) != (k1_funct_1 @ X16 @ X15))
% 0.45/0.63          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.45/0.63          | ~ (v1_funct_1 @ X16)
% 0.45/0.63          | ~ (v1_relat_1 @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X16)
% 0.45/0.63          | ~ (v1_funct_1 @ X16)
% 0.45/0.63          | (r2_hidden @ (k4_tarski @ X15 @ (k1_funct_1 @ X16 @ X15)) @ X16)
% 0.45/0.63          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['1'])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.45/0.63          | (r2_hidden @ 
% 0.45/0.63             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.45/0.63              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 0.45/0.63             X0)
% 0.45/0.63          | ~ (v1_funct_1 @ X0)
% 0.45/0.63          | ~ (v1_relat_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['0', '2'])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X0)
% 0.45/0.63          | ~ (v1_funct_1 @ X0)
% 0.45/0.63          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.45/0.63          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.63  thf(t143_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ C ) =>
% 0.45/0.63       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.45/0.63         ( ?[D:$i]:
% 0.45/0.63           ( ( r2_hidden @ D @ B ) & 
% 0.45/0.63             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.45/0.63             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.45/0.63          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ (k1_relat_1 @ X14))
% 0.45/0.63          | ~ (v1_relat_1 @ X14))),
% 0.45/0.63      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.45/0.63          | ~ (v1_relat_1 @ X1)
% 0.45/0.63          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.45/0.63             (k1_relat_1 @ X1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X0)
% 0.45/0.63          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.45/0.63          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_xboole_0 @ X0)
% 0.45/0.63          | ~ (v1_funct_1 @ X0)
% 0.45/0.63          | ~ (v1_relat_1 @ X0)
% 0.45/0.63          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.45/0.63          | ~ (v1_relat_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '10'])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.45/0.63          | ~ (v1_relat_1 @ X0)
% 0.45/0.63          | ~ (v1_funct_1 @ X0)
% 0.45/0.63          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.63  thf(t115_funct_2, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.63       ( ![E:$i]:
% 0.45/0.63         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.45/0.63              ( ![F:$i]:
% 0.45/0.63                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.45/0.63                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.63            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.63          ( ![E:$i]:
% 0.45/0.63            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.45/0.63                 ( ![F:$i]:
% 0.45/0.63                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.45/0.63                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k7_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.45/0.63          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.45/0.63           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('19', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['15', '18'])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      ((~ (v1_xboole_0 @ sk_D_1)
% 0.45/0.63        | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.63        | ~ (v1_relat_1 @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['12', '19'])).
% 0.45/0.63  thf('21', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc1_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( v1_relat_1 @ C ) ))).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.63         ((v1_relat_1 @ X18)
% 0.45/0.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.63  thf('24', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.63  thf('25', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.45/0.63      inference('demod', [status(thm)], ['20', '21', '24'])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.45/0.63           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('28', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t52_relset_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.45/0.63               ( ![D:$i]:
% 0.45/0.63                 ( ( m1_subset_1 @
% 0.45/0.63                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.45/0.63                   ( ![E:$i]:
% 0.45/0.63                     ( ( m1_subset_1 @ E @ A ) =>
% 0.45/0.63                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.45/0.63                         ( ?[F:$i]:
% 0.45/0.63                           ( ( r2_hidden @ F @ B ) & 
% 0.45/0.63                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.45/0.63                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ X35)
% 0.45/0.63          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.45/0.63          | ~ (r2_hidden @ X40 @ (k7_relset_1 @ X37 @ X38 @ X36 @ X35))
% 0.45/0.63          | (r2_hidden @ (k4_tarski @ (sk_F @ X40 @ X36 @ X37 @ X35) @ X40) @ 
% 0.45/0.63             X36)
% 0.45/0.63          | ~ (m1_subset_1 @ X40 @ X38)
% 0.45/0.63          | (v1_xboole_0 @ X37)
% 0.45/0.63          | (v1_xboole_0 @ X38))),
% 0.45/0.63      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.63          | (v1_xboole_0 @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.63          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.45/0.63             sk_D_1)
% 0.45/0.63          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.45/0.63          | (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.45/0.63           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.63          | (v1_xboole_0 @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.63          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.45/0.63             sk_D_1)
% 0.45/0.63          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.45/0.63          | (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_C)
% 0.45/0.63        | (r2_hidden @ 
% 0.45/0.63           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_E) @ sk_D_1)
% 0.45/0.63        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['28', '33'])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(dt_k7_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.45/0.63          | (m1_subset_1 @ (k7_relset_1 @ X28 @ X29 @ X27 @ X30) @ 
% 0.45/0.63             (k1_zfmisc_1 @ X29)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ 
% 0.45/0.63          (k1_zfmisc_1 @ sk_B_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.63  thf(t4_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.63       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X8 @ X9)
% 0.45/0.63          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.45/0.63          | (m1_subset_1 @ X8 @ X10))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X1 @ sk_B_1)
% 0.45/0.63          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.63  thf('41', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['35', '40'])).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_C)
% 0.45/0.63        | (r2_hidden @ 
% 0.45/0.63           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_E) @ sk_D_1)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['34', '41'])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.63         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.45/0.63          | ((X17) = (k1_funct_1 @ X16 @ X15))
% 0.45/0.63          | ~ (v1_funct_1 @ X16)
% 0.45/0.63          | ~ (v1_relat_1 @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_B_1)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_C)
% 0.45/0.63        | ~ (v1_relat_1 @ sk_D_1)
% 0.45/0.63        | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.63        | ((sk_E)
% 0.45/0.63            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.63  thf('45', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.63  thf('46', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_B_1)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_C)
% 0.45/0.63        | ((sk_E)
% 0.45/0.63            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.45/0.63      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.45/0.63  thf('48', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('50', plain,
% 0.45/0.63      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ X35)
% 0.45/0.63          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.45/0.63          | ~ (r2_hidden @ X40 @ (k7_relset_1 @ X37 @ X38 @ X36 @ X35))
% 0.45/0.63          | (r2_hidden @ (sk_F @ X40 @ X36 @ X37 @ X35) @ X35)
% 0.45/0.63          | ~ (m1_subset_1 @ X40 @ X38)
% 0.45/0.63          | (v1_xboole_0 @ X37)
% 0.45/0.63          | (v1_xboole_0 @ X38))),
% 0.45/0.63      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.63          | (v1_xboole_0 @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.63          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.45/0.63          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.45/0.63          | (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.63  thf('52', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.45/0.63           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('53', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.63          | (v1_xboole_0 @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.63          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.45/0.63          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.45/0.63          | (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_C)
% 0.45/0.63        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C)
% 0.45/0.63        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['48', '53'])).
% 0.45/0.63  thf('55', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['35', '40'])).
% 0.45/0.63  thf('56', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_C)
% 0.45/0.63        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['54', '55'])).
% 0.45/0.63  thf('57', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.63  thf('58', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('59', plain,
% 0.45/0.63      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ X35)
% 0.45/0.63          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.45/0.63          | ~ (r2_hidden @ X40 @ (k7_relset_1 @ X37 @ X38 @ X36 @ X35))
% 0.45/0.63          | (m1_subset_1 @ (sk_F @ X40 @ X36 @ X37 @ X35) @ X37)
% 0.45/0.63          | ~ (m1_subset_1 @ X40 @ X38)
% 0.45/0.63          | (v1_xboole_0 @ X37)
% 0.45/0.63          | (v1_xboole_0 @ X38))),
% 0.45/0.63      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.45/0.63  thf('60', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.63          | (v1_xboole_0 @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.63          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.45/0.63          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.45/0.63          | (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.63  thf('61', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.45/0.63           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('62', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.63          | (v1_xboole_0 @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.63          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.45/0.63          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.45/0.63          | (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.63  thf('63', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.45/0.63        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['57', '62'])).
% 0.45/0.63  thf('64', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['35', '40'])).
% 0.45/0.63  thf('65', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['63', '64'])).
% 0.45/0.63  thf(d2_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( v1_xboole_0 @ A ) =>
% 0.45/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.45/0.63       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.63  thf('66', plain,
% 0.45/0.63      (![X3 : $i, X4 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X3 @ X4)
% 0.45/0.63          | (r2_hidden @ X3 @ X4)
% 0.45/0.63          | (v1_xboole_0 @ X4))),
% 0.45/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.63  thf('67', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_B_1)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_C)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.63  thf('68', plain,
% 0.45/0.63      (((r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_C)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.63      inference('simplify', [status(thm)], ['67'])).
% 0.45/0.63  thf('69', plain,
% 0.45/0.63      (![X41 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X41 @ sk_A)
% 0.45/0.63          | ~ (r2_hidden @ X41 @ sk_C)
% 0.45/0.63          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X41)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('70', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_B_1)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_C)
% 0.45/0.63        | ((sk_E)
% 0.45/0.63            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.45/0.63        | ~ (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.63  thf('71', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_B_1)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_C)
% 0.45/0.63        | ((sk_E)
% 0.45/0.63            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.45/0.63        | (v1_xboole_0 @ sk_C)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['56', '70'])).
% 0.45/0.63  thf('72', plain,
% 0.45/0.63      ((((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.45/0.63        | (v1_xboole_0 @ sk_C)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.63      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.63  thf('73', plain,
% 0.45/0.63      ((((sk_E) != (sk_E))
% 0.45/0.63        | (v1_xboole_0 @ sk_C)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.45/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.45/0.63        | (v1_xboole_0 @ sk_A)
% 0.45/0.63        | (v1_xboole_0 @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['47', '72'])).
% 0.45/0.63  thf('74', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['73'])).
% 0.45/0.63  thf('75', plain,
% 0.45/0.63      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.63  thf('76', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.45/0.63          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 0.45/0.63          | ~ (v1_relat_1 @ X14))),
% 0.45/0.63      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.63  thf('77', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.45/0.63          | ~ (v1_relat_1 @ X1)
% 0.45/0.63          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.45/0.63             X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['75', '76'])).
% 0.45/0.63  thf('78', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.63  thf('79', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X1)
% 0.45/0.63          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.45/0.63          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.63  thf('80', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['15', '18'])).
% 0.45/0.63  thf('81', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['79', '80'])).
% 0.45/0.63  thf('82', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.63  thf('83', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.45/0.63      inference('demod', [status(thm)], ['81', '82'])).
% 0.45/0.63  thf('84', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.63      inference('clc', [status(thm)], ['74', '83'])).
% 0.45/0.63  thf('85', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc4_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_xboole_0 @ A ) =>
% 0.45/0.63       ( ![C:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.45/0.63           ( v1_xboole_0 @ C ) ) ) ))).
% 0.45/0.63  thf('86', plain,
% 0.45/0.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.63         (~ (v1_xboole_0 @ X24)
% 0.45/0.63          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 0.45/0.63          | (v1_xboole_0 @ X25))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.45/0.63  thf('87', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['85', '86'])).
% 0.45/0.63  thf('88', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['84', '87'])).
% 0.45/0.63  thf('89', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc3_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_xboole_0 @ A ) =>
% 0.45/0.63       ( ![C:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63           ( v1_xboole_0 @ C ) ) ) ))).
% 0.45/0.63  thf('90', plain,
% 0.45/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.63         (~ (v1_xboole_0 @ X21)
% 0.45/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X23)))
% 0.45/0.63          | (v1_xboole_0 @ X22))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.45/0.63  thf('91', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['89', '90'])).
% 0.45/0.63  thf('92', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.45/0.63      inference('clc', [status(thm)], ['88', '91'])).
% 0.45/0.63  thf('93', plain, ($false), inference('demod', [status(thm)], ['25', '92'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
