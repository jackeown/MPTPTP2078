%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6jkhEyQwYN

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:44 EST 2020

% Result     : Theorem 7.35s
% Output     : Refutation 7.35s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 305 expanded)
%              Number of leaves         :   40 ( 106 expanded)
%              Depth                    :   14
%              Number of atoms          : 1330 (4152 expanded)
%              Number of equality atoms :   25 ( 112 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k7_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k9_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['10','19'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X48: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( r2_hidden @ X48 @ ( k7_relset_1 @ X45 @ X46 @ X44 @ X43 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X48 @ X44 @ X45 @ X43 ) @ X48 ) @ X44 )
      | ~ ( m1_subset_1 @ X48 @ X46 )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_E ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_E ) @ sk_D_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','36'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X20 )
      | ( X21
        = ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('41',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('44',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X48: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( r2_hidden @ X48 @ ( k7_relset_1 @ X45 @ X46 @ X44 @ X43 ) )
      | ( m1_subset_1 @ ( sk_F @ X48 @ X44 @ X45 @ X43 ) @ X45 )
      | ~ ( m1_subset_1 @ X48 @ X46 )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['30','35'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X48: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( r2_hidden @ X48 @ ( k7_relset_1 @ X45 @ X46 @ X44 @ X43 ) )
      | ( r2_hidden @ ( sk_F @ X48 @ X44 @ X45 @ X43 ) @ X43 )
      | ~ ( m1_subset_1 @ X48 @ X46 )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['30','35'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X49: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X49 ) )
      | ~ ( r2_hidden @ X49 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X49 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('70',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X39 ) @ X40 )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('73',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('79',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['74','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('85',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('94',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k9_relat_1 @ X1 @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['89','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_D_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X1 @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X1 @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['105'])).

thf('107',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['83','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['22','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6jkhEyQwYN
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:00:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.35/7.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.35/7.56  % Solved by: fo/fo7.sh
% 7.35/7.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.35/7.56  % done 3223 iterations in 7.103s
% 7.35/7.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.35/7.56  % SZS output start Refutation
% 7.35/7.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 7.35/7.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.35/7.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 7.35/7.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.35/7.56  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 7.35/7.56  thf(sk_B_type, type, sk_B: $i > $i).
% 7.35/7.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.35/7.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 7.35/7.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.35/7.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.35/7.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.35/7.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.35/7.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.35/7.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.35/7.56  thf(sk_E_type, type, sk_E: $i).
% 7.35/7.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 7.35/7.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 7.35/7.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.35/7.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 7.35/7.56  thf(sk_A_type, type, sk_A: $i).
% 7.35/7.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 7.35/7.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.35/7.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.35/7.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.35/7.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.35/7.56  thf(t116_funct_2, conjecture,
% 7.35/7.56    (![A:$i,B:$i,C:$i,D:$i]:
% 7.35/7.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 7.35/7.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.35/7.56       ( ![E:$i]:
% 7.35/7.56         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 7.35/7.56              ( ![F:$i]:
% 7.35/7.56                ( ( m1_subset_1 @ F @ A ) =>
% 7.35/7.56                  ( ~( ( r2_hidden @ F @ C ) & 
% 7.35/7.56                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 7.35/7.56  thf(zf_stmt_0, negated_conjecture,
% 7.35/7.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 7.35/7.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 7.35/7.56            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.35/7.56          ( ![E:$i]:
% 7.35/7.56            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 7.35/7.56                 ( ![F:$i]:
% 7.35/7.56                   ( ( m1_subset_1 @ F @ A ) =>
% 7.35/7.56                     ( ~( ( r2_hidden @ F @ C ) & 
% 7.35/7.56                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 7.35/7.56    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 7.35/7.56  thf('0', plain,
% 7.35/7.56      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf('1', plain,
% 7.35/7.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf(redefinition_k7_relset_1, axiom,
% 7.35/7.56    (![A:$i,B:$i,C:$i,D:$i]:
% 7.35/7.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.35/7.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 7.35/7.56  thf('2', plain,
% 7.35/7.56      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 7.35/7.56         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 7.35/7.56          | ((k7_relset_1 @ X36 @ X37 @ X35 @ X38) = (k9_relat_1 @ X35 @ X38)))),
% 7.35/7.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 7.35/7.56  thf('3', plain,
% 7.35/7.56      (![X0 : $i]:
% 7.35/7.56         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 7.35/7.56           = (k9_relat_1 @ sk_D_1 @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['1', '2'])).
% 7.35/7.56  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 7.35/7.56      inference('demod', [status(thm)], ['0', '3'])).
% 7.35/7.56  thf(t143_relat_1, axiom,
% 7.35/7.56    (![A:$i,B:$i,C:$i]:
% 7.35/7.56     ( ( v1_relat_1 @ C ) =>
% 7.35/7.56       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 7.35/7.56         ( ?[D:$i]:
% 7.35/7.56           ( ( r2_hidden @ D @ B ) & 
% 7.35/7.56             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 7.35/7.56             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 7.35/7.56  thf('5', plain,
% 7.35/7.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 7.35/7.56         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 7.35/7.56          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ (k1_relat_1 @ X18))
% 7.35/7.56          | ~ (v1_relat_1 @ X18))),
% 7.35/7.56      inference('cnf', [status(esa)], [t143_relat_1])).
% 7.35/7.56  thf('6', plain,
% 7.35/7.56      ((~ (v1_relat_1 @ sk_D_1)
% 7.35/7.56        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 7.35/7.56      inference('sup-', [status(thm)], ['4', '5'])).
% 7.35/7.56  thf('7', plain,
% 7.35/7.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf(cc1_relset_1, axiom,
% 7.35/7.56    (![A:$i,B:$i,C:$i]:
% 7.35/7.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.35/7.56       ( v1_relat_1 @ C ) ))).
% 7.35/7.56  thf('8', plain,
% 7.35/7.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 7.35/7.56         ((v1_relat_1 @ X22)
% 7.35/7.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 7.35/7.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.35/7.56  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 7.35/7.56      inference('sup-', [status(thm)], ['7', '8'])).
% 7.35/7.56  thf('10', plain,
% 7.35/7.56      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 7.35/7.56      inference('demod', [status(thm)], ['6', '9'])).
% 7.35/7.56  thf('11', plain,
% 7.35/7.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf(cc2_relset_1, axiom,
% 7.35/7.56    (![A:$i,B:$i,C:$i]:
% 7.35/7.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.35/7.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 7.35/7.56  thf('12', plain,
% 7.35/7.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 7.35/7.56         ((v4_relat_1 @ X25 @ X26)
% 7.35/7.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 7.35/7.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.35/7.56  thf('13', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 7.35/7.56      inference('sup-', [status(thm)], ['11', '12'])).
% 7.35/7.56  thf(d18_relat_1, axiom,
% 7.35/7.56    (![A:$i,B:$i]:
% 7.35/7.56     ( ( v1_relat_1 @ B ) =>
% 7.35/7.56       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 7.35/7.56  thf('14', plain,
% 7.35/7.56      (![X13 : $i, X14 : $i]:
% 7.35/7.56         (~ (v4_relat_1 @ X13 @ X14)
% 7.35/7.56          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 7.35/7.56          | ~ (v1_relat_1 @ X13))),
% 7.35/7.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 7.35/7.56  thf('15', plain,
% 7.35/7.56      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 7.35/7.56      inference('sup-', [status(thm)], ['13', '14'])).
% 7.35/7.56  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 7.35/7.56      inference('sup-', [status(thm)], ['7', '8'])).
% 7.35/7.56  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 7.35/7.56      inference('demod', [status(thm)], ['15', '16'])).
% 7.35/7.56  thf(d3_tarski, axiom,
% 7.35/7.56    (![A:$i,B:$i]:
% 7.35/7.56     ( ( r1_tarski @ A @ B ) <=>
% 7.35/7.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.35/7.56  thf('18', plain,
% 7.35/7.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 7.35/7.56         (~ (r2_hidden @ X3 @ X4)
% 7.35/7.56          | (r2_hidden @ X3 @ X5)
% 7.35/7.56          | ~ (r1_tarski @ X4 @ X5))),
% 7.35/7.56      inference('cnf', [status(esa)], [d3_tarski])).
% 7.35/7.56  thf('19', plain,
% 7.35/7.56      (![X0 : $i]:
% 7.35/7.56         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 7.35/7.56      inference('sup-', [status(thm)], ['17', '18'])).
% 7.35/7.56  thf('20', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)),
% 7.35/7.56      inference('sup-', [status(thm)], ['10', '19'])).
% 7.35/7.56  thf(d1_xboole_0, axiom,
% 7.35/7.56    (![A:$i]:
% 7.35/7.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 7.35/7.56  thf('21', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 7.35/7.56  thf('22', plain, (~ (v1_xboole_0 @ sk_A)),
% 7.35/7.56      inference('sup-', [status(thm)], ['20', '21'])).
% 7.35/7.56  thf('23', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 7.35/7.56      inference('demod', [status(thm)], ['0', '3'])).
% 7.35/7.56  thf('24', plain,
% 7.35/7.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf(t52_relset_1, axiom,
% 7.35/7.56    (![A:$i]:
% 7.35/7.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.35/7.56       ( ![B:$i]:
% 7.35/7.56         ( ( ~( v1_xboole_0 @ B ) ) =>
% 7.35/7.56           ( ![C:$i]:
% 7.35/7.56             ( ( ~( v1_xboole_0 @ C ) ) =>
% 7.35/7.56               ( ![D:$i]:
% 7.35/7.56                 ( ( m1_subset_1 @
% 7.35/7.56                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 7.35/7.56                   ( ![E:$i]:
% 7.35/7.56                     ( ( m1_subset_1 @ E @ A ) =>
% 7.35/7.56                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 7.35/7.56                         ( ?[F:$i]:
% 7.35/7.56                           ( ( r2_hidden @ F @ B ) & 
% 7.35/7.56                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 7.35/7.56                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.35/7.56  thf('25', plain,
% 7.35/7.56      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X48 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ X43)
% 7.35/7.56          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 7.35/7.56          | ~ (r2_hidden @ X48 @ (k7_relset_1 @ X45 @ X46 @ X44 @ X43))
% 7.35/7.56          | (r2_hidden @ (k4_tarski @ (sk_F @ X48 @ X44 @ X45 @ X43) @ X48) @ 
% 7.35/7.56             X44)
% 7.35/7.56          | ~ (m1_subset_1 @ X48 @ X46)
% 7.35/7.56          | (v1_xboole_0 @ X45)
% 7.35/7.56          | (v1_xboole_0 @ X46))),
% 7.35/7.56      inference('cnf', [status(esa)], [t52_relset_1])).
% 7.35/7.56  thf('26', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ sk_B_1)
% 7.35/7.56          | (v1_xboole_0 @ sk_A)
% 7.35/7.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 7.35/7.56          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 7.35/7.56             sk_D_1)
% 7.35/7.56          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 7.35/7.56          | (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['24', '25'])).
% 7.35/7.56  thf('27', plain,
% 7.35/7.56      (![X0 : $i]:
% 7.35/7.56         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 7.35/7.56           = (k9_relat_1 @ sk_D_1 @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['1', '2'])).
% 7.35/7.56  thf('28', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ sk_B_1)
% 7.35/7.56          | (v1_xboole_0 @ sk_A)
% 7.35/7.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 7.35/7.56          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 7.35/7.56             sk_D_1)
% 7.35/7.56          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 7.35/7.56          | (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('demod', [status(thm)], ['26', '27'])).
% 7.35/7.56  thf('29', plain,
% 7.35/7.56      (((v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | (r2_hidden @ 
% 7.35/7.56           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_E) @ sk_D_1)
% 7.35/7.56        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_B_1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['23', '28'])).
% 7.35/7.56  thf('30', plain,
% 7.35/7.56      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf('31', plain,
% 7.35/7.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf(dt_k7_relset_1, axiom,
% 7.35/7.56    (![A:$i,B:$i,C:$i,D:$i]:
% 7.35/7.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.35/7.56       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 7.35/7.56  thf('32', plain,
% 7.35/7.56      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 7.35/7.56         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 7.35/7.56          | (m1_subset_1 @ (k7_relset_1 @ X32 @ X33 @ X31 @ X34) @ 
% 7.35/7.56             (k1_zfmisc_1 @ X33)))),
% 7.35/7.56      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 7.35/7.56  thf('33', plain,
% 7.35/7.56      (![X0 : $i]:
% 7.35/7.56         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ 
% 7.35/7.56          (k1_zfmisc_1 @ sk_B_1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['31', '32'])).
% 7.35/7.56  thf(t4_subset, axiom,
% 7.35/7.56    (![A:$i,B:$i,C:$i]:
% 7.35/7.56     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 7.35/7.56       ( m1_subset_1 @ A @ C ) ))).
% 7.35/7.56  thf('34', plain,
% 7.35/7.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 7.35/7.56         (~ (r2_hidden @ X10 @ X11)
% 7.35/7.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 7.35/7.56          | (m1_subset_1 @ X10 @ X12))),
% 7.35/7.56      inference('cnf', [status(esa)], [t4_subset])).
% 7.35/7.56  thf('35', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((m1_subset_1 @ X1 @ sk_B_1)
% 7.35/7.56          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 7.35/7.56      inference('sup-', [status(thm)], ['33', '34'])).
% 7.35/7.56  thf('36', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 7.35/7.56      inference('sup-', [status(thm)], ['30', '35'])).
% 7.35/7.56  thf('37', plain,
% 7.35/7.56      (((v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | (r2_hidden @ 
% 7.35/7.56           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_E) @ sk_D_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_B_1))),
% 7.35/7.56      inference('demod', [status(thm)], ['29', '36'])).
% 7.35/7.56  thf(t8_funct_1, axiom,
% 7.35/7.56    (![A:$i,B:$i,C:$i]:
% 7.35/7.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 7.35/7.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 7.35/7.56         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 7.35/7.56           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 7.35/7.56  thf('38', plain,
% 7.35/7.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.35/7.56         (~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X20)
% 7.35/7.56          | ((X21) = (k1_funct_1 @ X20 @ X19))
% 7.35/7.56          | ~ (v1_funct_1 @ X20)
% 7.35/7.56          | ~ (v1_relat_1 @ X20))),
% 7.35/7.56      inference('cnf', [status(esa)], [t8_funct_1])).
% 7.35/7.56  thf('39', plain,
% 7.35/7.56      (((v1_xboole_0 @ sk_B_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | ~ (v1_relat_1 @ sk_D_1)
% 7.35/7.56        | ~ (v1_funct_1 @ sk_D_1)
% 7.35/7.56        | ((sk_E)
% 7.35/7.56            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 7.35/7.56      inference('sup-', [status(thm)], ['37', '38'])).
% 7.35/7.56  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 7.35/7.56      inference('sup-', [status(thm)], ['7', '8'])).
% 7.35/7.56  thf('41', plain, ((v1_funct_1 @ sk_D_1)),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf('42', plain,
% 7.35/7.56      (((v1_xboole_0 @ sk_B_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | ((sk_E)
% 7.35/7.56            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 7.35/7.56      inference('demod', [status(thm)], ['39', '40', '41'])).
% 7.35/7.56  thf('43', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 7.35/7.56      inference('demod', [status(thm)], ['0', '3'])).
% 7.35/7.56  thf('44', plain,
% 7.35/7.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf('45', plain,
% 7.35/7.56      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X48 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ X43)
% 7.35/7.56          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 7.35/7.56          | ~ (r2_hidden @ X48 @ (k7_relset_1 @ X45 @ X46 @ X44 @ X43))
% 7.35/7.56          | (m1_subset_1 @ (sk_F @ X48 @ X44 @ X45 @ X43) @ X45)
% 7.35/7.56          | ~ (m1_subset_1 @ X48 @ X46)
% 7.35/7.56          | (v1_xboole_0 @ X45)
% 7.35/7.56          | (v1_xboole_0 @ X46))),
% 7.35/7.56      inference('cnf', [status(esa)], [t52_relset_1])).
% 7.35/7.56  thf('46', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ sk_B_1)
% 7.35/7.56          | (v1_xboole_0 @ sk_A)
% 7.35/7.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 7.35/7.56          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 7.35/7.56          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 7.35/7.56          | (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['44', '45'])).
% 7.35/7.56  thf('47', plain,
% 7.35/7.56      (![X0 : $i]:
% 7.35/7.56         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 7.35/7.56           = (k9_relat_1 @ sk_D_1 @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['1', '2'])).
% 7.35/7.56  thf('48', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ sk_B_1)
% 7.35/7.56          | (v1_xboole_0 @ sk_A)
% 7.35/7.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 7.35/7.56          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 7.35/7.56          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 7.35/7.56          | (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('demod', [status(thm)], ['46', '47'])).
% 7.35/7.56  thf('49', plain,
% 7.35/7.56      (((v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 7.35/7.56        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_B_1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['43', '48'])).
% 7.35/7.56  thf('50', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 7.35/7.56      inference('sup-', [status(thm)], ['30', '35'])).
% 7.35/7.56  thf('51', plain,
% 7.35/7.56      (((v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_B_1))),
% 7.35/7.56      inference('demod', [status(thm)], ['49', '50'])).
% 7.35/7.56  thf('52', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 7.35/7.56      inference('demod', [status(thm)], ['0', '3'])).
% 7.35/7.56  thf('53', plain,
% 7.35/7.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf('54', plain,
% 7.35/7.56      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X48 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ X43)
% 7.35/7.56          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 7.35/7.56          | ~ (r2_hidden @ X48 @ (k7_relset_1 @ X45 @ X46 @ X44 @ X43))
% 7.35/7.56          | (r2_hidden @ (sk_F @ X48 @ X44 @ X45 @ X43) @ X43)
% 7.35/7.56          | ~ (m1_subset_1 @ X48 @ X46)
% 7.35/7.56          | (v1_xboole_0 @ X45)
% 7.35/7.56          | (v1_xboole_0 @ X46))),
% 7.35/7.56      inference('cnf', [status(esa)], [t52_relset_1])).
% 7.35/7.56  thf('55', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ sk_B_1)
% 7.35/7.56          | (v1_xboole_0 @ sk_A)
% 7.35/7.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 7.35/7.56          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 7.35/7.56          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 7.35/7.56          | (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['53', '54'])).
% 7.35/7.56  thf('56', plain,
% 7.35/7.56      (![X0 : $i]:
% 7.35/7.56         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 7.35/7.56           = (k9_relat_1 @ sk_D_1 @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['1', '2'])).
% 7.35/7.56  thf('57', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ sk_B_1)
% 7.35/7.56          | (v1_xboole_0 @ sk_A)
% 7.35/7.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 7.35/7.56          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 7.35/7.56          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 7.35/7.56          | (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('demod', [status(thm)], ['55', '56'])).
% 7.35/7.56  thf('58', plain,
% 7.35/7.56      (((v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 7.35/7.56        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_B_1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['52', '57'])).
% 7.35/7.56  thf('59', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 7.35/7.56      inference('sup-', [status(thm)], ['30', '35'])).
% 7.35/7.56  thf('60', plain,
% 7.35/7.56      (((v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_B_1))),
% 7.35/7.56      inference('demod', [status(thm)], ['58', '59'])).
% 7.35/7.56  thf('61', plain,
% 7.35/7.56      (![X49 : $i]:
% 7.35/7.56         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X49))
% 7.35/7.56          | ~ (r2_hidden @ X49 @ sk_C_1)
% 7.35/7.56          | ~ (m1_subset_1 @ X49 @ sk_A))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf('62', plain,
% 7.35/7.56      (((v1_xboole_0 @ sk_B_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | ~ (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 7.35/7.56        | ((sk_E)
% 7.35/7.56            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 7.35/7.56      inference('sup-', [status(thm)], ['60', '61'])).
% 7.35/7.56  thf('63', plain,
% 7.35/7.56      (((v1_xboole_0 @ sk_B_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | ((sk_E)
% 7.35/7.56            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1)))
% 7.35/7.56        | (v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_B_1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['51', '62'])).
% 7.35/7.56  thf('64', plain,
% 7.35/7.56      ((((sk_E)
% 7.35/7.56          != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1)))
% 7.35/7.56        | (v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_B_1))),
% 7.35/7.56      inference('simplify', [status(thm)], ['63'])).
% 7.35/7.56  thf('65', plain,
% 7.35/7.56      ((((sk_E) != (sk_E))
% 7.35/7.56        | (v1_xboole_0 @ sk_C_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_B_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_B_1)
% 7.35/7.56        | (v1_xboole_0 @ sk_A)
% 7.35/7.56        | (v1_xboole_0 @ sk_C_1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['42', '64'])).
% 7.35/7.56  thf('66', plain,
% 7.35/7.56      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 7.35/7.56      inference('simplify', [status(thm)], ['65'])).
% 7.35/7.56  thf(d10_xboole_0, axiom,
% 7.35/7.56    (![A:$i,B:$i]:
% 7.35/7.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.35/7.56  thf('67', plain,
% 7.35/7.56      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 7.35/7.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.35/7.56  thf('68', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 7.35/7.56      inference('simplify', [status(thm)], ['67'])).
% 7.35/7.56  thf('69', plain,
% 7.35/7.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf(t13_relset_1, axiom,
% 7.35/7.56    (![A:$i,B:$i,C:$i,D:$i]:
% 7.35/7.56     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 7.35/7.56       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 7.35/7.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 7.35/7.56  thf('70', plain,
% 7.35/7.56      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 7.35/7.56         (~ (r1_tarski @ (k1_relat_1 @ X39) @ X40)
% 7.35/7.56          | (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 7.35/7.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 7.35/7.56      inference('cnf', [status(esa)], [t13_relset_1])).
% 7.35/7.56  thf('71', plain,
% 7.35/7.56      (![X0 : $i]:
% 7.35/7.56         ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 7.35/7.56          | ~ (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['69', '70'])).
% 7.35/7.56  thf('72', plain,
% 7.35/7.56      ((m1_subset_1 @ sk_D_1 @ 
% 7.35/7.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B_1)))),
% 7.35/7.56      inference('sup-', [status(thm)], ['68', '71'])).
% 7.35/7.56  thf(cc4_relset_1, axiom,
% 7.35/7.56    (![A:$i,B:$i]:
% 7.35/7.56     ( ( v1_xboole_0 @ A ) =>
% 7.35/7.56       ( ![C:$i]:
% 7.35/7.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 7.35/7.56           ( v1_xboole_0 @ C ) ) ) ))).
% 7.35/7.56  thf('73', plain,
% 7.35/7.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 7.35/7.56         (~ (v1_xboole_0 @ X28)
% 7.35/7.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 7.35/7.56          | (v1_xboole_0 @ X29))),
% 7.35/7.56      inference('cnf', [status(esa)], [cc4_relset_1])).
% 7.35/7.56  thf('74', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['72', '73'])).
% 7.35/7.56  thf('75', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 7.35/7.56      inference('demod', [status(thm)], ['0', '3'])).
% 7.35/7.56  thf('76', plain,
% 7.35/7.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 7.35/7.56         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 7.35/7.56          | (r2_hidden @ (k4_tarski @ (sk_D @ X18 @ X16 @ X17) @ X17) @ X18)
% 7.35/7.56          | ~ (v1_relat_1 @ X18))),
% 7.35/7.56      inference('cnf', [status(esa)], [t143_relat_1])).
% 7.35/7.56  thf('77', plain,
% 7.35/7.56      ((~ (v1_relat_1 @ sk_D_1)
% 7.35/7.56        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 7.35/7.56           sk_D_1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['75', '76'])).
% 7.35/7.56  thf('78', plain, ((v1_relat_1 @ sk_D_1)),
% 7.35/7.56      inference('sup-', [status(thm)], ['7', '8'])).
% 7.35/7.56  thf('79', plain,
% 7.35/7.56      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 7.35/7.56        sk_D_1)),
% 7.35/7.56      inference('demod', [status(thm)], ['77', '78'])).
% 7.35/7.56  thf('80', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 7.35/7.56  thf('81', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 7.35/7.56      inference('sup-', [status(thm)], ['79', '80'])).
% 7.35/7.56  thf('82', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 7.35/7.56      inference('clc', [status(thm)], ['74', '81'])).
% 7.35/7.56  thf('83', plain, (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_A))),
% 7.35/7.56      inference('clc', [status(thm)], ['66', '82'])).
% 7.35/7.56  thf('84', plain, ((v1_relat_1 @ sk_D_1)),
% 7.35/7.56      inference('sup-', [status(thm)], ['7', '8'])).
% 7.35/7.56  thf('85', plain,
% 7.35/7.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 7.35/7.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 7.35/7.56  thf('86', plain,
% 7.35/7.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 7.35/7.56         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 7.35/7.56          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ X16)
% 7.35/7.56          | ~ (v1_relat_1 @ X18))),
% 7.35/7.56      inference('cnf', [status(esa)], [t143_relat_1])).
% 7.35/7.56  thf('87', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 7.35/7.56          | ~ (v1_relat_1 @ X1)
% 7.35/7.56          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 7.35/7.56             X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['85', '86'])).
% 7.35/7.56  thf('88', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 7.35/7.56  thf('89', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         (~ (v1_relat_1 @ X1)
% 7.35/7.56          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 7.35/7.56          | ~ (v1_xboole_0 @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['87', '88'])).
% 7.35/7.56  thf('90', plain,
% 7.35/7.56      (![X4 : $i, X6 : $i]:
% 7.35/7.56         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 7.35/7.56      inference('cnf', [status(esa)], [d3_tarski])).
% 7.35/7.56  thf('91', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 7.35/7.56  thf('92', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['90', '91'])).
% 7.35/7.56  thf('93', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['90', '91'])).
% 7.35/7.56  thf('94', plain,
% 7.35/7.56      (![X7 : $i, X9 : $i]:
% 7.35/7.56         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 7.35/7.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.35/7.56  thf('95', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 7.35/7.56      inference('sup-', [status(thm)], ['93', '94'])).
% 7.35/7.56  thf('96', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['92', '95'])).
% 7.35/7.56  thf('97', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.35/7.56         (~ (v1_xboole_0 @ X0)
% 7.35/7.56          | ~ (v1_relat_1 @ X1)
% 7.35/7.56          | ~ (v1_xboole_0 @ X2)
% 7.35/7.56          | ((k9_relat_1 @ X1 @ X0) = (X2)))),
% 7.35/7.56      inference('sup-', [status(thm)], ['89', '96'])).
% 7.35/7.56  thf('98', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         (((k9_relat_1 @ sk_D_1 @ X0) = (X1))
% 7.35/7.56          | ~ (v1_xboole_0 @ X1)
% 7.35/7.56          | ~ (v1_xboole_0 @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['84', '97'])).
% 7.35/7.56  thf('99', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 7.35/7.56          | ~ (v1_relat_1 @ X1)
% 7.35/7.56          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 7.35/7.56             X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['85', '86'])).
% 7.35/7.56  thf('100', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((r2_hidden @ (sk_D @ sk_D_1 @ X1 @ (sk_B @ X0)) @ X1)
% 7.35/7.56          | ~ (v1_xboole_0 @ X1)
% 7.35/7.56          | ~ (v1_xboole_0 @ X0)
% 7.35/7.56          | ~ (v1_relat_1 @ sk_D_1)
% 7.35/7.56          | (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X1)))),
% 7.35/7.56      inference('sup+', [status(thm)], ['98', '99'])).
% 7.35/7.56  thf('101', plain, ((v1_relat_1 @ sk_D_1)),
% 7.35/7.56      inference('sup-', [status(thm)], ['7', '8'])).
% 7.35/7.56  thf('102', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((r2_hidden @ (sk_D @ sk_D_1 @ X1 @ (sk_B @ X0)) @ X1)
% 7.35/7.56          | ~ (v1_xboole_0 @ X1)
% 7.35/7.56          | ~ (v1_xboole_0 @ X0)
% 7.35/7.56          | (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X1)))),
% 7.35/7.56      inference('demod', [status(thm)], ['100', '101'])).
% 7.35/7.56  thf('103', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 7.35/7.56  thf('104', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0))
% 7.35/7.56          | ~ (v1_xboole_0 @ X1)
% 7.35/7.56          | ~ (v1_xboole_0 @ X0)
% 7.35/7.56          | ~ (v1_xboole_0 @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['102', '103'])).
% 7.35/7.56  thf('105', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]:
% 7.35/7.56         (~ (v1_xboole_0 @ X0)
% 7.35/7.56          | ~ (v1_xboole_0 @ X1)
% 7.35/7.56          | (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 7.35/7.56      inference('simplify', [status(thm)], ['104'])).
% 7.35/7.56  thf('106', plain,
% 7.35/7.56      (![X0 : $i]:
% 7.35/7.56         ((v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 7.35/7.56      inference('condensation', [status(thm)], ['105'])).
% 7.35/7.56  thf('107', plain,
% 7.35/7.56      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 7.35/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.35/7.56  thf('108', plain,
% 7.35/7.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 7.35/7.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 7.35/7.56  thf('109', plain,
% 7.35/7.56      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 7.35/7.56      inference('sup-', [status(thm)], ['107', '108'])).
% 7.35/7.56  thf('110', plain,
% 7.35/7.56      (![X0 : $i]:
% 7.35/7.56         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 7.35/7.56           = (k9_relat_1 @ sk_D_1 @ X0))),
% 7.35/7.56      inference('sup-', [status(thm)], ['1', '2'])).
% 7.35/7.56  thf('111', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 7.35/7.56      inference('demod', [status(thm)], ['109', '110'])).
% 7.35/7.56  thf('112', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 7.35/7.56      inference('sup-', [status(thm)], ['106', '111'])).
% 7.35/7.56  thf('113', plain, ((v1_xboole_0 @ sk_A)),
% 7.35/7.56      inference('clc', [status(thm)], ['83', '112'])).
% 7.35/7.56  thf('114', plain, ($false), inference('demod', [status(thm)], ['22', '113'])).
% 7.35/7.56  
% 7.35/7.56  % SZS output end Refutation
% 7.35/7.56  
% 7.35/7.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
