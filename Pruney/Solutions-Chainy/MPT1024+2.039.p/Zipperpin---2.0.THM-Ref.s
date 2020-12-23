%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wocJH13QM4

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:39 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 257 expanded)
%              Number of leaves         :   34 (  89 expanded)
%              Depth                    :   17
%              Number of atoms          : 1196 (3615 expanded)
%              Number of equality atoms :   19 (  95 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( X21
       != ( k1_funct_1 @ X20 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( k1_funct_1 @ X20 @ X19 ) ) @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['20','21','26'])).

thf('28',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('30',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X41: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_hidden @ X41 @ ( k7_relset_1 @ X38 @ X39 @ X37 @ X36 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X41 @ X37 @ X38 @ X36 ) @ X41 ) @ X37 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 ) ) ),
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
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_E ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
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
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_E ) @ sk_D_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X20 )
      | ( X21
        = ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
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
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('51',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X41: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_hidden @ X41 @ ( k7_relset_1 @ X38 @ X39 @ X37 @ X36 ) )
      | ( r2_hidden @ ( sk_F @ X41 @ X37 @ X38 @ X36 ) @ X36 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 ) ) ),
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
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','42'])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('60',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X41: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_hidden @ X41 @ ( k7_relset_1 @ X38 @ X39 @ X37 @ X36 ) )
      | ( m1_subset_1 @ ( sk_F @ X41 @ X37 @ X38 @ X36 ) @ X38 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 ) ) ),
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
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','42'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_A )
      | ~ ( r2_hidden @ X42 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ~ ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','72'])).

thf('74',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('78',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ( v1_xboole_0 @ X26 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wocJH13QM4
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.69  % Solved by: fo/fo7.sh
% 0.48/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.69  % done 308 iterations in 0.236s
% 0.48/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.69  % SZS output start Refutation
% 0.48/0.69  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.48/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.48/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.69  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.48/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.48/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.48/0.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.48/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.48/0.69  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.48/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.48/0.70  thf(sk_E_type, type, sk_E: $i).
% 0.48/0.70  thf(d1_xboole_0, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.70  thf('0', plain,
% 0.48/0.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.48/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.70  thf(t8_funct_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.48/0.70       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.48/0.70         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.48/0.70           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.48/0.70  thf('1', plain,
% 0.48/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X19 @ (k1_relat_1 @ X20))
% 0.48/0.70          | ((X21) != (k1_funct_1 @ X20 @ X19))
% 0.48/0.70          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ X20)
% 0.48/0.70          | ~ (v1_funct_1 @ X20)
% 0.48/0.70          | ~ (v1_relat_1 @ X20))),
% 0.48/0.70      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.48/0.70  thf('2', plain,
% 0.48/0.70      (![X19 : $i, X20 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X20)
% 0.48/0.70          | ~ (v1_funct_1 @ X20)
% 0.48/0.70          | (r2_hidden @ (k4_tarski @ X19 @ (k1_funct_1 @ X20 @ X19)) @ X20)
% 0.48/0.70          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X20)))),
% 0.48/0.70      inference('simplify', [status(thm)], ['1'])).
% 0.48/0.70  thf('3', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.48/0.70          | (r2_hidden @ 
% 0.48/0.70             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.48/0.70              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 0.48/0.70             X0)
% 0.48/0.70          | ~ (v1_funct_1 @ X0)
% 0.48/0.70          | ~ (v1_relat_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['0', '2'])).
% 0.48/0.70  thf('4', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.48/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.70  thf('5', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X0)
% 0.48/0.70          | ~ (v1_funct_1 @ X0)
% 0.48/0.70          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.48/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.48/0.70  thf('6', plain,
% 0.48/0.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.48/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.70  thf(t143_relat_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( v1_relat_1 @ C ) =>
% 0.48/0.70       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.48/0.70         ( ?[D:$i]:
% 0.48/0.70           ( ( r2_hidden @ D @ B ) & 
% 0.48/0.70             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.48/0.70             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.48/0.70  thf('7', plain,
% 0.48/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.48/0.70          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ (k1_relat_1 @ X18))
% 0.48/0.70          | ~ (v1_relat_1 @ X18))),
% 0.48/0.70      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.48/0.70  thf('8', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.48/0.70          | ~ (v1_relat_1 @ X1)
% 0.48/0.70          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.48/0.70             (k1_relat_1 @ X1)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.48/0.70  thf('9', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.48/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.70  thf('10', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X0)
% 0.48/0.70          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.48/0.70          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.70  thf('11', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         (~ (v1_xboole_0 @ X0)
% 0.48/0.70          | ~ (v1_funct_1 @ X0)
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.48/0.70          | ~ (v1_relat_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['5', '10'])).
% 0.48/0.70  thf('12', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ~ (v1_funct_1 @ X0)
% 0.48/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['11'])).
% 0.48/0.70  thf(t115_funct_2, conjecture,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.70       ( ![E:$i]:
% 0.48/0.70         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.48/0.70              ( ![F:$i]:
% 0.48/0.70                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.48/0.70                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.48/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.70        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.70            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.70          ( ![E:$i]:
% 0.48/0.70            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.48/0.70                 ( ![F:$i]:
% 0.48/0.70                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.48/0.70                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.48/0.70    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.48/0.70  thf('13', plain,
% 0.48/0.70      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('14', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.48/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.70  thf('15', plain,
% 0.48/0.70      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.48/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.70  thf('16', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(redefinition_k7_relset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.48/0.70  thf('17', plain,
% 0.48/0.70      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.48/0.70          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.48/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.48/0.70  thf('18', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.48/0.70           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.70  thf('19', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.48/0.70      inference('demod', [status(thm)], ['15', '18'])).
% 0.48/0.70  thf('20', plain,
% 0.48/0.70      ((~ (v1_xboole_0 @ sk_D_1)
% 0.48/0.70        | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.70        | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['12', '19'])).
% 0.48/0.70  thf('21', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('22', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(cc2_relat_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( v1_relat_1 @ A ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.48/0.70  thf('23', plain,
% 0.48/0.70      (![X11 : $i, X12 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.48/0.70          | (v1_relat_1 @ X11)
% 0.48/0.70          | ~ (v1_relat_1 @ X12))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.70  thf('24', plain,
% 0.48/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['22', '23'])).
% 0.48/0.70  thf(fc6_relat_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.48/0.70  thf('25', plain,
% 0.48/0.70      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.48/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.48/0.70  thf('26', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['24', '25'])).
% 0.48/0.70  thf('27', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['20', '21', '26'])).
% 0.48/0.70  thf('28', plain,
% 0.48/0.70      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('29', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.48/0.70           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.70  thf('30', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.48/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.48/0.70  thf('31', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(t52_relset_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.48/0.70           ( ![C:$i]:
% 0.48/0.70             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.48/0.70               ( ![D:$i]:
% 0.48/0.70                 ( ( m1_subset_1 @
% 0.48/0.70                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.48/0.70                   ( ![E:$i]:
% 0.48/0.70                     ( ( m1_subset_1 @ E @ A ) =>
% 0.48/0.70                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.48/0.70                         ( ?[F:$i]:
% 0.48/0.70                           ( ( r2_hidden @ F @ B ) & 
% 0.48/0.70                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.48/0.70                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.70  thf('32', plain,
% 0.48/0.70      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X41 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ X36)
% 0.48/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.48/0.70          | ~ (r2_hidden @ X41 @ (k7_relset_1 @ X38 @ X39 @ X37 @ X36))
% 0.48/0.70          | (r2_hidden @ (k4_tarski @ (sk_F @ X41 @ X37 @ X38 @ X36) @ X41) @ 
% 0.48/0.70             X37)
% 0.48/0.70          | ~ (m1_subset_1 @ X41 @ X39)
% 0.48/0.70          | (v1_xboole_0 @ X38)
% 0.48/0.70          | (v1_xboole_0 @ X39))),
% 0.48/0.70      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.48/0.70  thf('33', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ sk_B_1)
% 0.48/0.70          | (v1_xboole_0 @ sk_A)
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.48/0.70          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.48/0.70             sk_D_1)
% 0.48/0.70          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.48/0.70          | (v1_xboole_0 @ X1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.70  thf('34', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.48/0.70           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.70  thf('35', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ sk_B_1)
% 0.48/0.70          | (v1_xboole_0 @ sk_A)
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.48/0.70          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.48/0.70             sk_D_1)
% 0.48/0.70          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.48/0.70          | (v1_xboole_0 @ X1))),
% 0.48/0.70      inference('demod', [status(thm)], ['33', '34'])).
% 0.48/0.70  thf('36', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_C)
% 0.48/0.70        | (r2_hidden @ 
% 0.48/0.70           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_E) @ sk_D_1)
% 0.48/0.70        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['30', '35'])).
% 0.48/0.70  thf('37', plain,
% 0.48/0.70      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('38', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(dt_k7_relset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.48/0.70  thf('39', plain,
% 0.48/0.70      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.48/0.70          | (m1_subset_1 @ (k7_relset_1 @ X29 @ X30 @ X28 @ X31) @ 
% 0.48/0.70             (k1_zfmisc_1 @ X30)))),
% 0.48/0.70      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.48/0.70  thf('40', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ 
% 0.48/0.70          (k1_zfmisc_1 @ sk_B_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['38', '39'])).
% 0.48/0.70  thf(t4_subset, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.48/0.70       ( m1_subset_1 @ A @ C ) ))).
% 0.48/0.70  thf('41', plain,
% 0.48/0.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X8 @ X9)
% 0.48/0.70          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.48/0.70          | (m1_subset_1 @ X8 @ X10))),
% 0.48/0.70      inference('cnf', [status(esa)], [t4_subset])).
% 0.48/0.70  thf('42', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((m1_subset_1 @ X1 @ sk_B_1)
% 0.48/0.70          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['40', '41'])).
% 0.48/0.70  thf('43', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.48/0.70      inference('sup-', [status(thm)], ['37', '42'])).
% 0.48/0.70  thf('44', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_C)
% 0.48/0.70        | (r2_hidden @ 
% 0.48/0.70           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_E) @ sk_D_1)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.70      inference('demod', [status(thm)], ['36', '43'])).
% 0.48/0.70  thf('45', plain,
% 0.48/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.70         (~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X20)
% 0.48/0.70          | ((X21) = (k1_funct_1 @ X20 @ X19))
% 0.48/0.70          | ~ (v1_funct_1 @ X20)
% 0.48/0.70          | ~ (v1_relat_1 @ X20))),
% 0.48/0.70      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.48/0.70  thf('46', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_B_1)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | ~ (v1_relat_1 @ sk_D_1)
% 0.48/0.70        | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.70        | ((sk_E)
% 0.48/0.70            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.48/0.70  thf('47', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['24', '25'])).
% 0.48/0.70  thf('48', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('49', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_B_1)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | ((sk_E)
% 0.48/0.70            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.48/0.70      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.48/0.70  thf('50', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.48/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.48/0.70  thf('51', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('52', plain,
% 0.48/0.70      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X41 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ X36)
% 0.48/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.48/0.70          | ~ (r2_hidden @ X41 @ (k7_relset_1 @ X38 @ X39 @ X37 @ X36))
% 0.48/0.70          | (r2_hidden @ (sk_F @ X41 @ X37 @ X38 @ X36) @ X36)
% 0.48/0.70          | ~ (m1_subset_1 @ X41 @ X39)
% 0.48/0.70          | (v1_xboole_0 @ X38)
% 0.48/0.70          | (v1_xboole_0 @ X39))),
% 0.48/0.70      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.48/0.70  thf('53', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ sk_B_1)
% 0.48/0.70          | (v1_xboole_0 @ sk_A)
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.48/0.70          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.48/0.70          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.48/0.70          | (v1_xboole_0 @ X1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.48/0.70  thf('54', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.48/0.70           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.70  thf('55', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ sk_B_1)
% 0.48/0.70          | (v1_xboole_0 @ sk_A)
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.48/0.70          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.48/0.70          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.48/0.70          | (v1_xboole_0 @ X1))),
% 0.48/0.70      inference('demod', [status(thm)], ['53', '54'])).
% 0.48/0.70  thf('56', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_C)
% 0.48/0.70        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C)
% 0.48/0.70        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['50', '55'])).
% 0.48/0.70  thf('57', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.48/0.70      inference('sup-', [status(thm)], ['37', '42'])).
% 0.48/0.70  thf('58', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_C)
% 0.48/0.70        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.70      inference('demod', [status(thm)], ['56', '57'])).
% 0.48/0.70  thf('59', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.48/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.48/0.70  thf('60', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('61', plain,
% 0.48/0.70      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X41 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ X36)
% 0.48/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.48/0.70          | ~ (r2_hidden @ X41 @ (k7_relset_1 @ X38 @ X39 @ X37 @ X36))
% 0.48/0.70          | (m1_subset_1 @ (sk_F @ X41 @ X37 @ X38 @ X36) @ X38)
% 0.48/0.70          | ~ (m1_subset_1 @ X41 @ X39)
% 0.48/0.70          | (v1_xboole_0 @ X38)
% 0.48/0.70          | (v1_xboole_0 @ X39))),
% 0.48/0.70      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.48/0.70  thf('62', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ sk_B_1)
% 0.48/0.70          | (v1_xboole_0 @ sk_A)
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.48/0.70          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.48/0.70          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.48/0.70          | (v1_xboole_0 @ X1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.48/0.70  thf('63', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.48/0.70           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.70  thf('64', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ sk_B_1)
% 0.48/0.70          | (v1_xboole_0 @ sk_A)
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.48/0.70          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.48/0.70          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.48/0.70          | (v1_xboole_0 @ X1))),
% 0.48/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.48/0.70  thf('65', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_C)
% 0.48/0.70        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.48/0.70        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['59', '64'])).
% 0.48/0.70  thf('66', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.48/0.70      inference('sup-', [status(thm)], ['37', '42'])).
% 0.48/0.70  thf('67', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_C)
% 0.48/0.70        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.70      inference('demod', [status(thm)], ['65', '66'])).
% 0.48/0.70  thf(d2_subset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( ( v1_xboole_0 @ A ) =>
% 0.48/0.70         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.48/0.70       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.70         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.70  thf('68', plain,
% 0.48/0.70      (![X3 : $i, X4 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X3 @ X4)
% 0.48/0.70          | (r2_hidden @ X3 @ X4)
% 0.48/0.70          | (v1_xboole_0 @ X4))),
% 0.48/0.70      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.48/0.70  thf('69', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_B_1)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['67', '68'])).
% 0.48/0.70  thf('70', plain,
% 0.48/0.70      (((r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.70      inference('simplify', [status(thm)], ['69'])).
% 0.48/0.70  thf('71', plain,
% 0.48/0.70      (![X42 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X42 @ sk_A)
% 0.48/0.70          | ~ (r2_hidden @ X42 @ sk_C)
% 0.48/0.70          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X42)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('72', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_B_1)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | ((sk_E)
% 0.48/0.70            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.48/0.70        | ~ (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C))),
% 0.48/0.70      inference('sup-', [status(thm)], ['70', '71'])).
% 0.48/0.70  thf('73', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_B_1)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | ((sk_E)
% 0.48/0.70            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['58', '72'])).
% 0.48/0.70  thf('74', plain,
% 0.48/0.70      ((((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.70      inference('simplify', [status(thm)], ['73'])).
% 0.48/0.70  thf('75', plain,
% 0.48/0.70      ((((sk_E) != (sk_E))
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.70        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_C))),
% 0.48/0.70      inference('sup-', [status(thm)], ['49', '74'])).
% 0.48/0.70  thf('76', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 0.48/0.70      inference('simplify', [status(thm)], ['75'])).
% 0.48/0.70  thf('77', plain,
% 0.48/0.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.48/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.70  thf('78', plain,
% 0.48/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.48/0.70          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ X16)
% 0.48/0.70          | ~ (v1_relat_1 @ X18))),
% 0.48/0.70      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.48/0.70  thf('79', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.48/0.70          | ~ (v1_relat_1 @ X1)
% 0.48/0.70          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.48/0.70             X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['77', '78'])).
% 0.48/0.70  thf('80', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.48/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.70  thf('81', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X1)
% 0.48/0.70          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.48/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['79', '80'])).
% 0.48/0.70  thf('82', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.48/0.70      inference('demod', [status(thm)], ['15', '18'])).
% 0.48/0.70  thf('83', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['81', '82'])).
% 0.48/0.70  thf('84', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['24', '25'])).
% 0.48/0.70  thf('85', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.48/0.70      inference('demod', [status(thm)], ['83', '84'])).
% 0.48/0.70  thf('86', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.70      inference('clc', [status(thm)], ['76', '85'])).
% 0.48/0.70  thf('87', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(cc4_relset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( v1_xboole_0 @ A ) =>
% 0.48/0.70       ( ![C:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.48/0.70           ( v1_xboole_0 @ C ) ) ) ))).
% 0.48/0.70  thf('88', plain,
% 0.48/0.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.48/0.70         (~ (v1_xboole_0 @ X25)
% 0.48/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.48/0.70          | (v1_xboole_0 @ X26))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.48/0.70  thf('89', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['87', '88'])).
% 0.48/0.70  thf('90', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['86', '89'])).
% 0.48/0.70  thf('91', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(cc3_relset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( v1_xboole_0 @ A ) =>
% 0.48/0.70       ( ![C:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70           ( v1_xboole_0 @ C ) ) ) ))).
% 0.48/0.70  thf('92', plain,
% 0.48/0.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.48/0.70         (~ (v1_xboole_0 @ X22)
% 0.48/0.70          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 0.48/0.70          | (v1_xboole_0 @ X23))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.48/0.70  thf('93', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['91', '92'])).
% 0.48/0.70  thf('94', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.48/0.70      inference('clc', [status(thm)], ['90', '93'])).
% 0.48/0.70  thf('95', plain, ($false), inference('demod', [status(thm)], ['27', '94'])).
% 0.48/0.70  
% 0.48/0.70  % SZS output end Refutation
% 0.48/0.70  
% 0.48/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
