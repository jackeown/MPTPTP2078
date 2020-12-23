%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H1mIbhlGN7

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:34 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 221 expanded)
%              Number of leaves         :   32 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          : 1018 (3306 expanded)
%              Number of equality atoms :   17 (  91 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

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

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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

thf('15',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_hidden @ X40 @ ( k7_relset_1 @ X37 @ X38 @ X36 @ X35 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X40 @ X36 @ X37 @ X35 ) @ X40 ) @ X36 )
      | ~ ( m1_subset_1 @ X40 @ X38 )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_E ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B_2 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ sk_B_2 ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_E ) @ sk_D_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['19','26'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( X17
        = ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('31',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('34',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_hidden @ X40 @ ( k7_relset_1 @ X37 @ X38 @ X36 @ X35 ) )
      | ( r2_hidden @ ( sk_F @ X40 @ X36 @ X37 @ X35 ) @ X35 )
      | ~ ( m1_subset_1 @ X40 @ X38 )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ sk_B_2 ),
    inference('sup-',[status(thm)],['20','25'])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_hidden @ X40 @ ( k7_relset_1 @ X37 @ X38 @ X36 @ X35 ) )
      | ( m1_subset_1 @ ( sk_F @ X40 @ X36 @ X37 @ X35 ) @ X37 )
      | ~ ( m1_subset_1 @ X40 @ X38 )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_E @ sk_B_2 ),
    inference('sup-',[status(thm)],['20','25'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_A )
      | ~ ( r2_hidden @ X41 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ~ ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('64',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['59','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('69',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('73',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X23 ) ) )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['71','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['12','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H1mIbhlGN7
% 0.16/0.36  % Computer   : n006.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 20:05:38 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.54/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.76  % Solved by: fo/fo7.sh
% 0.54/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.76  % done 293 iterations in 0.284s
% 0.54/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.76  % SZS output start Refutation
% 0.54/0.76  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.54/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.76  thf(sk_E_type, type, sk_E: $i).
% 0.54/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.76  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.54/0.76  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.54/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.76  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.54/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.76  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.54/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.76  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.54/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.76  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.54/0.76  thf(t115_funct_2, conjecture,
% 0.54/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.76       ( ![E:$i]:
% 0.54/0.76         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.54/0.76              ( ![F:$i]:
% 0.54/0.76                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.54/0.76                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.76    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.76            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.76          ( ![E:$i]:
% 0.54/0.76            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.54/0.76                 ( ![F:$i]:
% 0.54/0.76                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.54/0.76                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.54/0.76    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.54/0.76  thf('0', plain,
% 0.54/0.76      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('1', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(redefinition_k7_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.54/0.76  thf('2', plain,
% 0.54/0.76      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.54/0.76          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.54/0.76  thf('3', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.54/0.76           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.76  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.54/0.76      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.76  thf(t143_relat_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ C ) =>
% 0.54/0.76       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.54/0.76         ( ?[D:$i]:
% 0.54/0.76           ( ( r2_hidden @ D @ B ) & 
% 0.54/0.76             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.54/0.76             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.54/0.76  thf('5', plain,
% 0.54/0.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.54/0.76          | (r2_hidden @ (k4_tarski @ (sk_D @ X14 @ X12 @ X13) @ X13) @ X14)
% 0.54/0.76          | ~ (v1_relat_1 @ X14))),
% 0.54/0.76      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.54/0.76  thf('6', plain,
% 0.54/0.76      ((~ (v1_relat_1 @ sk_D_1)
% 0.54/0.76        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.54/0.76           sk_D_1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.76  thf('7', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(cc1_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( v1_relat_1 @ C ) ))).
% 0.54/0.76  thf('8', plain,
% 0.54/0.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.76         ((v1_relat_1 @ X18)
% 0.54/0.76          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.76  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 0.54/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.76  thf('10', plain,
% 0.54/0.76      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.54/0.76      inference('demod', [status(thm)], ['6', '9'])).
% 0.54/0.76  thf(d1_xboole_0, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.54/0.76  thf('11', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.76      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.76  thf('12', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.54/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.76  thf('13', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.54/0.76      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.76  thf('14', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(t52_relset_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.76           ( ![C:$i]:
% 0.54/0.76             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.54/0.76               ( ![D:$i]:
% 0.54/0.76                 ( ( m1_subset_1 @
% 0.54/0.76                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.54/0.76                   ( ![E:$i]:
% 0.54/0.76                     ( ( m1_subset_1 @ E @ A ) =>
% 0.54/0.76                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.54/0.76                         ( ?[F:$i]:
% 0.54/0.76                           ( ( r2_hidden @ F @ B ) & 
% 0.54/0.76                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.54/0.76                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.76  thf('15', plain,
% 0.54/0.76      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ X35)
% 0.54/0.76          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.54/0.76          | ~ (r2_hidden @ X40 @ (k7_relset_1 @ X37 @ X38 @ X36 @ X35))
% 0.54/0.76          | (r2_hidden @ (k4_tarski @ (sk_F @ X40 @ X36 @ X37 @ X35) @ X40) @ 
% 0.54/0.76             X36)
% 0.54/0.76          | ~ (m1_subset_1 @ X40 @ X38)
% 0.54/0.76          | (v1_xboole_0 @ X37)
% 0.54/0.76          | (v1_xboole_0 @ X38))),
% 0.54/0.76      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.54/0.76  thf('16', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ sk_B_2)
% 0.54/0.76          | (v1_xboole_0 @ sk_A)
% 0.54/0.76          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.54/0.76          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.54/0.76             sk_D_1)
% 0.54/0.76          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1))
% 0.54/0.76          | (v1_xboole_0 @ X1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.76  thf('17', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.54/0.76           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.76  thf('18', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ sk_B_2)
% 0.54/0.76          | (v1_xboole_0 @ sk_A)
% 0.54/0.76          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.54/0.76          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.54/0.76             sk_D_1)
% 0.54/0.76          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.54/0.76          | (v1_xboole_0 @ X1))),
% 0.54/0.76      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.76  thf('19', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_C)
% 0.54/0.76        | (r2_hidden @ 
% 0.54/0.76           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_E) @ sk_D_1)
% 0.54/0.76        | ~ (m1_subset_1 @ sk_E @ sk_B_2)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['13', '18'])).
% 0.54/0.76  thf('20', plain,
% 0.54/0.76      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('21', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(dt_k7_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.54/0.76  thf('22', plain,
% 0.54/0.76      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.54/0.76          | (m1_subset_1 @ (k7_relset_1 @ X28 @ X29 @ X27 @ X30) @ 
% 0.54/0.76             (k1_zfmisc_1 @ X29)))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.54/0.76  thf('23', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0) @ 
% 0.54/0.76          (k1_zfmisc_1 @ sk_B_2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.76  thf(t4_subset, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.54/0.76       ( m1_subset_1 @ A @ C ) ))).
% 0.54/0.76  thf('24', plain,
% 0.54/0.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X8 @ X9)
% 0.54/0.76          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.54/0.76          | (m1_subset_1 @ X8 @ X10))),
% 0.54/0.76      inference('cnf', [status(esa)], [t4_subset])).
% 0.54/0.76  thf('25', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         ((m1_subset_1 @ X1 @ sk_B_2)
% 0.54/0.76          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.76  thf('26', plain, ((m1_subset_1 @ sk_E @ sk_B_2)),
% 0.54/0.76      inference('sup-', [status(thm)], ['20', '25'])).
% 0.54/0.76  thf('27', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_C)
% 0.54/0.76        | (r2_hidden @ 
% 0.54/0.76           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_E) @ sk_D_1)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.76      inference('demod', [status(thm)], ['19', '26'])).
% 0.54/0.76  thf(t8_funct_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.54/0.76       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.54/0.76         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.54/0.76           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.54/0.76  thf('28', plain,
% 0.54/0.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.54/0.76         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.54/0.76          | ((X17) = (k1_funct_1 @ X16 @ X15))
% 0.54/0.76          | ~ (v1_funct_1 @ X16)
% 0.54/0.76          | ~ (v1_relat_1 @ X16))),
% 0.54/0.76      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.54/0.76  thf('29', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_B_2)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_C)
% 0.54/0.76        | ~ (v1_relat_1 @ sk_D_1)
% 0.54/0.76        | ~ (v1_funct_1 @ sk_D_1)
% 0.54/0.76        | ((sk_E)
% 0.54/0.76            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['27', '28'])).
% 0.54/0.76  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.54/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.76  thf('31', plain, ((v1_funct_1 @ sk_D_1)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('32', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_B_2)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_C)
% 0.54/0.76        | ((sk_E)
% 0.54/0.76            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.54/0.76      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.54/0.76  thf('33', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.54/0.76      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.76  thf('34', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('35', plain,
% 0.54/0.76      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ X35)
% 0.54/0.76          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.54/0.76          | ~ (r2_hidden @ X40 @ (k7_relset_1 @ X37 @ X38 @ X36 @ X35))
% 0.54/0.76          | (r2_hidden @ (sk_F @ X40 @ X36 @ X37 @ X35) @ X35)
% 0.54/0.76          | ~ (m1_subset_1 @ X40 @ X38)
% 0.54/0.76          | (v1_xboole_0 @ X37)
% 0.54/0.76          | (v1_xboole_0 @ X38))),
% 0.54/0.76      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.54/0.76  thf('36', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ sk_B_2)
% 0.54/0.76          | (v1_xboole_0 @ sk_A)
% 0.54/0.76          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.54/0.76          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.54/0.76          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1))
% 0.54/0.76          | (v1_xboole_0 @ X1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['34', '35'])).
% 0.54/0.76  thf('37', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.54/0.76           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.76  thf('38', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ sk_B_2)
% 0.54/0.76          | (v1_xboole_0 @ sk_A)
% 0.54/0.76          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.54/0.76          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.54/0.76          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.54/0.76          | (v1_xboole_0 @ X1))),
% 0.54/0.76      inference('demod', [status(thm)], ['36', '37'])).
% 0.54/0.76  thf('39', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_C)
% 0.54/0.76        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C)
% 0.54/0.76        | ~ (m1_subset_1 @ sk_E @ sk_B_2)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['33', '38'])).
% 0.54/0.76  thf('40', plain, ((m1_subset_1 @ sk_E @ sk_B_2)),
% 0.54/0.76      inference('sup-', [status(thm)], ['20', '25'])).
% 0.54/0.76  thf('41', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_C)
% 0.54/0.76        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.76      inference('demod', [status(thm)], ['39', '40'])).
% 0.54/0.76  thf('42', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.54/0.76      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.76  thf('43', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('44', plain,
% 0.54/0.76      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ X35)
% 0.54/0.76          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.54/0.76          | ~ (r2_hidden @ X40 @ (k7_relset_1 @ X37 @ X38 @ X36 @ X35))
% 0.54/0.76          | (m1_subset_1 @ (sk_F @ X40 @ X36 @ X37 @ X35) @ X37)
% 0.54/0.76          | ~ (m1_subset_1 @ X40 @ X38)
% 0.54/0.76          | (v1_xboole_0 @ X37)
% 0.54/0.76          | (v1_xboole_0 @ X38))),
% 0.54/0.76      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.54/0.76  thf('45', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ sk_B_2)
% 0.54/0.76          | (v1_xboole_0 @ sk_A)
% 0.54/0.76          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.54/0.76          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.54/0.76          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1))
% 0.54/0.76          | (v1_xboole_0 @ X1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['43', '44'])).
% 0.54/0.76  thf('46', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.54/0.76           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.76  thf('47', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ sk_B_2)
% 0.54/0.76          | (v1_xboole_0 @ sk_A)
% 0.54/0.76          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.54/0.76          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.54/0.76          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.54/0.76          | (v1_xboole_0 @ X1))),
% 0.54/0.76      inference('demod', [status(thm)], ['45', '46'])).
% 0.54/0.76  thf('48', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_C)
% 0.54/0.76        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.54/0.76        | ~ (m1_subset_1 @ sk_E @ sk_B_2)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['42', '47'])).
% 0.54/0.76  thf('49', plain, ((m1_subset_1 @ sk_E @ sk_B_2)),
% 0.54/0.76      inference('sup-', [status(thm)], ['20', '25'])).
% 0.54/0.76  thf('50', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_C)
% 0.54/0.76        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.76      inference('demod', [status(thm)], ['48', '49'])).
% 0.54/0.76  thf(t2_subset, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ A @ B ) =>
% 0.54/0.76       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.54/0.76  thf('51', plain,
% 0.54/0.76      (![X6 : $i, X7 : $i]:
% 0.54/0.76         ((r2_hidden @ X6 @ X7)
% 0.54/0.76          | (v1_xboole_0 @ X7)
% 0.54/0.76          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.54/0.76      inference('cnf', [status(esa)], [t2_subset])).
% 0.54/0.76  thf('52', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_B_2)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_C)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['50', '51'])).
% 0.54/0.76  thf('53', plain,
% 0.54/0.76      (((r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_C)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.76      inference('simplify', [status(thm)], ['52'])).
% 0.54/0.76  thf('54', plain,
% 0.54/0.76      (![X41 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X41 @ sk_A)
% 0.54/0.76          | ~ (r2_hidden @ X41 @ sk_C)
% 0.54/0.76          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X41)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('55', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_B_2)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_C)
% 0.54/0.76        | ((sk_E)
% 0.54/0.76            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.54/0.76        | ~ (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.76  thf('56', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_B_2)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_C)
% 0.54/0.76        | ((sk_E)
% 0.54/0.76            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.54/0.76        | (v1_xboole_0 @ sk_C)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['41', '55'])).
% 0.54/0.76  thf('57', plain,
% 0.54/0.76      ((((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.54/0.76        | (v1_xboole_0 @ sk_C)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.76      inference('simplify', [status(thm)], ['56'])).
% 0.54/0.76  thf('58', plain,
% 0.54/0.76      ((((sk_E) != (sk_E))
% 0.54/0.76        | (v1_xboole_0 @ sk_C)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_B_2)
% 0.54/0.76        | (v1_xboole_0 @ sk_B_2)
% 0.54/0.76        | (v1_xboole_0 @ sk_A)
% 0.54/0.76        | (v1_xboole_0 @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['32', '57'])).
% 0.54/0.76  thf('59', plain,
% 0.54/0.76      (((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 0.54/0.76      inference('simplify', [status(thm)], ['58'])).
% 0.54/0.76  thf('60', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.54/0.76      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.76  thf('61', plain,
% 0.54/0.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.54/0.76          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 0.54/0.76          | ~ (v1_relat_1 @ X14))),
% 0.54/0.76      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.54/0.76  thf('62', plain,
% 0.54/0.76      ((~ (v1_relat_1 @ sk_D_1)
% 0.54/0.76        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['60', '61'])).
% 0.54/0.76  thf('63', plain, ((v1_relat_1 @ sk_D_1)),
% 0.54/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.76  thf('64', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.54/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.54/0.76  thf('65', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.76      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.76  thf('66', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.54/0.76      inference('sup-', [status(thm)], ['64', '65'])).
% 0.54/0.76  thf('67', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.76      inference('clc', [status(thm)], ['59', '66'])).
% 0.54/0.76  thf('68', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(cc4_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( v1_xboole_0 @ A ) =>
% 0.54/0.76       ( ![C:$i]:
% 0.54/0.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.54/0.76           ( v1_xboole_0 @ C ) ) ) ))).
% 0.54/0.76  thf('69', plain,
% 0.54/0.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ X24)
% 0.54/0.76          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 0.54/0.76          | (v1_xboole_0 @ X25))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.54/0.76  thf('70', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_B_2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['68', '69'])).
% 0.54/0.76  thf('71', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D_1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['67', '70'])).
% 0.54/0.76  thf('72', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(cc3_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( v1_xboole_0 @ A ) =>
% 0.54/0.76       ( ![C:$i]:
% 0.54/0.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76           ( v1_xboole_0 @ C ) ) ) ))).
% 0.54/0.76  thf('73', plain,
% 0.54/0.76      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ X21)
% 0.54/0.76          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X23)))
% 0.54/0.76          | (v1_xboole_0 @ X22))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.54/0.76  thf('74', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['72', '73'])).
% 0.54/0.76  thf('75', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.54/0.76      inference('clc', [status(thm)], ['71', '74'])).
% 0.54/0.76  thf('76', plain, ($false), inference('demod', [status(thm)], ['12', '75'])).
% 0.54/0.76  
% 0.54/0.76  % SZS output end Refutation
% 0.54/0.76  
% 0.54/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
