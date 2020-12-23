%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.arhYVadqGU

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:44 EST 2020

% Result     : Theorem 6.03s
% Output     : Refutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 345 expanded)
%              Number of leaves         :   39 ( 118 expanded)
%              Depth                    :   14
%              Number of atoms          : 1374 (4804 expanded)
%              Number of equality atoms :   27 ( 131 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X44: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_hidden @ X44 @ ( k7_relset_1 @ X41 @ X42 @ X40 @ X39 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X44 @ X40 @ X41 @ X39 ) @ X44 ) @ X40 )
      | ~ ( m1_subset_1 @ X44 @ X42 )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X42 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X44: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_hidden @ X44 @ ( k7_relset_1 @ X41 @ X42 @ X40 @ X39 ) )
      | ( m1_subset_1 @ ( sk_F @ X44 @ X40 @ X41 @ X39 ) @ X41 )
      | ~ ( m1_subset_1 @ X44 @ X42 )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X42 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X44: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_hidden @ X44 @ ( k7_relset_1 @ X41 @ X42 @ X40 @ X39 ) )
      | ( r2_hidden @ ( sk_F @ X44 @ X40 @ X41 @ X39 ) @ X39 )
      | ~ ( m1_subset_1 @ X44 @ X42 )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X42 ) ) ),
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
    ! [X45: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X45 ) )
      | ~ ( r2_hidden @ X45 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X45 @ sk_A ) ) ),
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

thf('67',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('69',plain,(
    v5_relat_1 @ sk_D_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('71',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X19 ) @ X21 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v5_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v5_relat_1 @ sk_D_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('74',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('80',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('84',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['75','85'])).

thf('87',plain,(
    r2_hidden @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['69','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('92',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('93',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('101',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k9_relat_1 @ X1 @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['96','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_D_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X1 @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X1 @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['112'])).

thf('114',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('116',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('118',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['90','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['22','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.arhYVadqGU
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 6.03/6.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.03/6.23  % Solved by: fo/fo7.sh
% 6.03/6.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.03/6.23  % done 2710 iterations in 5.780s
% 6.03/6.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.03/6.23  % SZS output start Refutation
% 6.03/6.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.03/6.23  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.03/6.23  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.03/6.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.03/6.23  thf(sk_B_type, type, sk_B: $i > $i).
% 6.03/6.23  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 6.03/6.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.03/6.23  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.03/6.23  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.03/6.23  thf(sk_E_type, type, sk_E: $i).
% 6.03/6.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.03/6.23  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.03/6.23  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.03/6.23  thf(sk_D_1_type, type, sk_D_1: $i).
% 6.03/6.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.03/6.23  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.03/6.23  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 6.03/6.23  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.03/6.23  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.03/6.23  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.03/6.23  thf(sk_A_type, type, sk_A: $i).
% 6.03/6.23  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.03/6.23  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.03/6.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.03/6.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.03/6.23  thf(t116_funct_2, conjecture,
% 6.03/6.23    (![A:$i,B:$i,C:$i,D:$i]:
% 6.03/6.23     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.03/6.23         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.03/6.23       ( ![E:$i]:
% 6.03/6.23         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 6.03/6.23              ( ![F:$i]:
% 6.03/6.23                ( ( m1_subset_1 @ F @ A ) =>
% 6.03/6.23                  ( ~( ( r2_hidden @ F @ C ) & 
% 6.03/6.23                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 6.03/6.23  thf(zf_stmt_0, negated_conjecture,
% 6.03/6.23    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 6.03/6.23        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.03/6.23            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.03/6.23          ( ![E:$i]:
% 6.03/6.23            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 6.03/6.23                 ( ![F:$i]:
% 6.03/6.23                   ( ( m1_subset_1 @ F @ A ) =>
% 6.03/6.23                     ( ~( ( r2_hidden @ F @ C ) & 
% 6.03/6.23                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 6.03/6.23    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 6.03/6.23  thf('0', plain,
% 6.03/6.23      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf('1', plain,
% 6.03/6.23      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf(redefinition_k7_relset_1, axiom,
% 6.03/6.23    (![A:$i,B:$i,C:$i,D:$i]:
% 6.03/6.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.03/6.23       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 6.03/6.23  thf('2', plain,
% 6.03/6.23      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 6.03/6.23         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 6.03/6.23          | ((k7_relset_1 @ X36 @ X37 @ X35 @ X38) = (k9_relat_1 @ X35 @ X38)))),
% 6.03/6.23      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 6.03/6.23  thf('3', plain,
% 6.03/6.23      (![X0 : $i]:
% 6.03/6.23         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 6.03/6.23           = (k9_relat_1 @ sk_D_1 @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['1', '2'])).
% 6.03/6.23  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 6.03/6.23      inference('demod', [status(thm)], ['0', '3'])).
% 6.03/6.23  thf(t143_relat_1, axiom,
% 6.03/6.23    (![A:$i,B:$i,C:$i]:
% 6.03/6.23     ( ( v1_relat_1 @ C ) =>
% 6.03/6.23       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 6.03/6.23         ( ?[D:$i]:
% 6.03/6.23           ( ( r2_hidden @ D @ B ) & 
% 6.03/6.23             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 6.03/6.23             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 6.03/6.23  thf('5', plain,
% 6.03/6.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.03/6.23         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 6.03/6.23          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ (k1_relat_1 @ X18))
% 6.03/6.23          | ~ (v1_relat_1 @ X18))),
% 6.03/6.23      inference('cnf', [status(esa)], [t143_relat_1])).
% 6.03/6.23  thf('6', plain,
% 6.03/6.23      ((~ (v1_relat_1 @ sk_D_1)
% 6.03/6.23        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 6.03/6.23      inference('sup-', [status(thm)], ['4', '5'])).
% 6.03/6.23  thf('7', plain,
% 6.03/6.23      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf(cc1_relset_1, axiom,
% 6.03/6.23    (![A:$i,B:$i,C:$i]:
% 6.03/6.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.03/6.23       ( v1_relat_1 @ C ) ))).
% 6.03/6.23  thf('8', plain,
% 6.03/6.23      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.03/6.23         ((v1_relat_1 @ X25)
% 6.03/6.23          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 6.03/6.23      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.03/6.23  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['7', '8'])).
% 6.03/6.23  thf('10', plain,
% 6.03/6.23      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 6.03/6.23      inference('demod', [status(thm)], ['6', '9'])).
% 6.03/6.23  thf('11', plain,
% 6.03/6.23      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf(cc2_relset_1, axiom,
% 6.03/6.23    (![A:$i,B:$i,C:$i]:
% 6.03/6.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.03/6.23       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.03/6.23  thf('12', plain,
% 6.03/6.23      (![X28 : $i, X29 : $i, X30 : $i]:
% 6.03/6.23         ((v4_relat_1 @ X28 @ X29)
% 6.03/6.23          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 6.03/6.23      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.03/6.23  thf('13', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 6.03/6.23      inference('sup-', [status(thm)], ['11', '12'])).
% 6.03/6.23  thf(d18_relat_1, axiom,
% 6.03/6.23    (![A:$i,B:$i]:
% 6.03/6.23     ( ( v1_relat_1 @ B ) =>
% 6.03/6.23       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 6.03/6.23  thf('14', plain,
% 6.03/6.23      (![X13 : $i, X14 : $i]:
% 6.03/6.23         (~ (v4_relat_1 @ X13 @ X14)
% 6.03/6.23          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 6.03/6.23          | ~ (v1_relat_1 @ X13))),
% 6.03/6.23      inference('cnf', [status(esa)], [d18_relat_1])).
% 6.03/6.23  thf('15', plain,
% 6.03/6.23      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 6.03/6.23      inference('sup-', [status(thm)], ['13', '14'])).
% 6.03/6.23  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['7', '8'])).
% 6.03/6.23  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 6.03/6.23      inference('demod', [status(thm)], ['15', '16'])).
% 6.03/6.23  thf(d3_tarski, axiom,
% 6.03/6.23    (![A:$i,B:$i]:
% 6.03/6.23     ( ( r1_tarski @ A @ B ) <=>
% 6.03/6.23       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.03/6.23  thf('18', plain,
% 6.03/6.23      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.03/6.23         (~ (r2_hidden @ X3 @ X4)
% 6.03/6.23          | (r2_hidden @ X3 @ X5)
% 6.03/6.23          | ~ (r1_tarski @ X4 @ X5))),
% 6.03/6.23      inference('cnf', [status(esa)], [d3_tarski])).
% 6.03/6.23  thf('19', plain,
% 6.03/6.23      (![X0 : $i]:
% 6.03/6.23         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 6.03/6.23      inference('sup-', [status(thm)], ['17', '18'])).
% 6.03/6.23  thf('20', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)),
% 6.03/6.23      inference('sup-', [status(thm)], ['10', '19'])).
% 6.03/6.23  thf(d1_xboole_0, axiom,
% 6.03/6.23    (![A:$i]:
% 6.03/6.23     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 6.03/6.23  thf('21', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.03/6.23  thf('22', plain, (~ (v1_xboole_0 @ sk_A)),
% 6.03/6.23      inference('sup-', [status(thm)], ['20', '21'])).
% 6.03/6.23  thf('23', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 6.03/6.23      inference('demod', [status(thm)], ['0', '3'])).
% 6.03/6.23  thf('24', plain,
% 6.03/6.23      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf(t52_relset_1, axiom,
% 6.03/6.23    (![A:$i]:
% 6.03/6.23     ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.03/6.23       ( ![B:$i]:
% 6.03/6.23         ( ( ~( v1_xboole_0 @ B ) ) =>
% 6.03/6.23           ( ![C:$i]:
% 6.03/6.23             ( ( ~( v1_xboole_0 @ C ) ) =>
% 6.03/6.23               ( ![D:$i]:
% 6.03/6.23                 ( ( m1_subset_1 @
% 6.03/6.23                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 6.03/6.23                   ( ![E:$i]:
% 6.03/6.23                     ( ( m1_subset_1 @ E @ A ) =>
% 6.03/6.23                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 6.03/6.23                         ( ?[F:$i]:
% 6.03/6.23                           ( ( r2_hidden @ F @ B ) & 
% 6.03/6.23                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 6.03/6.23                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.03/6.23  thf('25', plain,
% 6.03/6.23      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X44 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ X39)
% 6.03/6.23          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 6.03/6.23          | ~ (r2_hidden @ X44 @ (k7_relset_1 @ X41 @ X42 @ X40 @ X39))
% 6.03/6.23          | (r2_hidden @ (k4_tarski @ (sk_F @ X44 @ X40 @ X41 @ X39) @ X44) @ 
% 6.03/6.23             X40)
% 6.03/6.23          | ~ (m1_subset_1 @ X44 @ X42)
% 6.03/6.23          | (v1_xboole_0 @ X41)
% 6.03/6.23          | (v1_xboole_0 @ X42))),
% 6.03/6.23      inference('cnf', [status(esa)], [t52_relset_1])).
% 6.03/6.23  thf('26', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ sk_B_1)
% 6.03/6.23          | (v1_xboole_0 @ sk_A)
% 6.03/6.23          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 6.03/6.23          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 6.03/6.23             sk_D_1)
% 6.03/6.23          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 6.03/6.23          | (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('sup-', [status(thm)], ['24', '25'])).
% 6.03/6.23  thf('27', plain,
% 6.03/6.23      (![X0 : $i]:
% 6.03/6.23         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 6.03/6.23           = (k9_relat_1 @ sk_D_1 @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['1', '2'])).
% 6.03/6.23  thf('28', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ sk_B_1)
% 6.03/6.23          | (v1_xboole_0 @ sk_A)
% 6.03/6.23          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 6.03/6.23          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 6.03/6.23             sk_D_1)
% 6.03/6.23          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 6.03/6.23          | (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('demod', [status(thm)], ['26', '27'])).
% 6.03/6.23  thf('29', plain,
% 6.03/6.23      (((v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | (r2_hidden @ 
% 6.03/6.23           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_E) @ sk_D_1)
% 6.03/6.23        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_B_1))),
% 6.03/6.23      inference('sup-', [status(thm)], ['23', '28'])).
% 6.03/6.23  thf('30', plain,
% 6.03/6.23      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf('31', plain,
% 6.03/6.23      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf(dt_k7_relset_1, axiom,
% 6.03/6.23    (![A:$i,B:$i,C:$i,D:$i]:
% 6.03/6.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.03/6.23       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 6.03/6.23  thf('32', plain,
% 6.03/6.23      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 6.03/6.23         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 6.03/6.23          | (m1_subset_1 @ (k7_relset_1 @ X32 @ X33 @ X31 @ X34) @ 
% 6.03/6.23             (k1_zfmisc_1 @ X33)))),
% 6.03/6.23      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 6.03/6.23  thf('33', plain,
% 6.03/6.23      (![X0 : $i]:
% 6.03/6.23         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ 
% 6.03/6.23          (k1_zfmisc_1 @ sk_B_1))),
% 6.03/6.23      inference('sup-', [status(thm)], ['31', '32'])).
% 6.03/6.23  thf(t4_subset, axiom,
% 6.03/6.23    (![A:$i,B:$i,C:$i]:
% 6.03/6.23     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 6.03/6.23       ( m1_subset_1 @ A @ C ) ))).
% 6.03/6.23  thf('34', plain,
% 6.03/6.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.03/6.23         (~ (r2_hidden @ X10 @ X11)
% 6.03/6.23          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 6.03/6.23          | (m1_subset_1 @ X10 @ X12))),
% 6.03/6.23      inference('cnf', [status(esa)], [t4_subset])).
% 6.03/6.23  thf('35', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((m1_subset_1 @ X1 @ sk_B_1)
% 6.03/6.23          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 6.03/6.23      inference('sup-', [status(thm)], ['33', '34'])).
% 6.03/6.23  thf('36', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['30', '35'])).
% 6.03/6.23  thf('37', plain,
% 6.03/6.23      (((v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | (r2_hidden @ 
% 6.03/6.23           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_E) @ sk_D_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_B_1))),
% 6.03/6.23      inference('demod', [status(thm)], ['29', '36'])).
% 6.03/6.23  thf(t8_funct_1, axiom,
% 6.03/6.23    (![A:$i,B:$i,C:$i]:
% 6.03/6.23     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 6.03/6.23       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 6.03/6.23         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 6.03/6.23           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 6.03/6.23  thf('38', plain,
% 6.03/6.23      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.03/6.23         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 6.03/6.23          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 6.03/6.23          | ~ (v1_funct_1 @ X23)
% 6.03/6.23          | ~ (v1_relat_1 @ X23))),
% 6.03/6.23      inference('cnf', [status(esa)], [t8_funct_1])).
% 6.03/6.23  thf('39', plain,
% 6.03/6.23      (((v1_xboole_0 @ sk_B_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | ~ (v1_relat_1 @ sk_D_1)
% 6.03/6.23        | ~ (v1_funct_1 @ sk_D_1)
% 6.03/6.23        | ((sk_E)
% 6.03/6.23            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 6.03/6.23      inference('sup-', [status(thm)], ['37', '38'])).
% 6.03/6.23  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['7', '8'])).
% 6.03/6.23  thf('41', plain, ((v1_funct_1 @ sk_D_1)),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf('42', plain,
% 6.03/6.23      (((v1_xboole_0 @ sk_B_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | ((sk_E)
% 6.03/6.23            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 6.03/6.23      inference('demod', [status(thm)], ['39', '40', '41'])).
% 6.03/6.23  thf('43', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 6.03/6.23      inference('demod', [status(thm)], ['0', '3'])).
% 6.03/6.23  thf('44', plain,
% 6.03/6.23      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf('45', plain,
% 6.03/6.23      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X44 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ X39)
% 6.03/6.23          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 6.03/6.23          | ~ (r2_hidden @ X44 @ (k7_relset_1 @ X41 @ X42 @ X40 @ X39))
% 6.03/6.23          | (m1_subset_1 @ (sk_F @ X44 @ X40 @ X41 @ X39) @ X41)
% 6.03/6.23          | ~ (m1_subset_1 @ X44 @ X42)
% 6.03/6.23          | (v1_xboole_0 @ X41)
% 6.03/6.23          | (v1_xboole_0 @ X42))),
% 6.03/6.23      inference('cnf', [status(esa)], [t52_relset_1])).
% 6.03/6.23  thf('46', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ sk_B_1)
% 6.03/6.23          | (v1_xboole_0 @ sk_A)
% 6.03/6.23          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 6.03/6.23          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 6.03/6.23          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 6.03/6.23          | (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('sup-', [status(thm)], ['44', '45'])).
% 6.03/6.23  thf('47', plain,
% 6.03/6.23      (![X0 : $i]:
% 6.03/6.23         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 6.03/6.23           = (k9_relat_1 @ sk_D_1 @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['1', '2'])).
% 6.03/6.23  thf('48', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ sk_B_1)
% 6.03/6.23          | (v1_xboole_0 @ sk_A)
% 6.03/6.23          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 6.03/6.23          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 6.03/6.23          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 6.03/6.23          | (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('demod', [status(thm)], ['46', '47'])).
% 6.03/6.23  thf('49', plain,
% 6.03/6.23      (((v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 6.03/6.23        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_B_1))),
% 6.03/6.23      inference('sup-', [status(thm)], ['43', '48'])).
% 6.03/6.23  thf('50', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['30', '35'])).
% 6.03/6.23  thf('51', plain,
% 6.03/6.23      (((v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_B_1))),
% 6.03/6.23      inference('demod', [status(thm)], ['49', '50'])).
% 6.03/6.23  thf('52', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 6.03/6.23      inference('demod', [status(thm)], ['0', '3'])).
% 6.03/6.23  thf('53', plain,
% 6.03/6.23      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf('54', plain,
% 6.03/6.23      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X44 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ X39)
% 6.03/6.23          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 6.03/6.23          | ~ (r2_hidden @ X44 @ (k7_relset_1 @ X41 @ X42 @ X40 @ X39))
% 6.03/6.23          | (r2_hidden @ (sk_F @ X44 @ X40 @ X41 @ X39) @ X39)
% 6.03/6.23          | ~ (m1_subset_1 @ X44 @ X42)
% 6.03/6.23          | (v1_xboole_0 @ X41)
% 6.03/6.23          | (v1_xboole_0 @ X42))),
% 6.03/6.23      inference('cnf', [status(esa)], [t52_relset_1])).
% 6.03/6.23  thf('55', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ sk_B_1)
% 6.03/6.23          | (v1_xboole_0 @ sk_A)
% 6.03/6.23          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 6.03/6.23          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 6.03/6.23          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 6.03/6.23          | (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('sup-', [status(thm)], ['53', '54'])).
% 6.03/6.23  thf('56', plain,
% 6.03/6.23      (![X0 : $i]:
% 6.03/6.23         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 6.03/6.23           = (k9_relat_1 @ sk_D_1 @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['1', '2'])).
% 6.03/6.23  thf('57', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ sk_B_1)
% 6.03/6.23          | (v1_xboole_0 @ sk_A)
% 6.03/6.23          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 6.03/6.23          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 6.03/6.23          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 6.03/6.23          | (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('demod', [status(thm)], ['55', '56'])).
% 6.03/6.23  thf('58', plain,
% 6.03/6.23      (((v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 6.03/6.23        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_B_1))),
% 6.03/6.23      inference('sup-', [status(thm)], ['52', '57'])).
% 6.03/6.23  thf('59', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['30', '35'])).
% 6.03/6.23  thf('60', plain,
% 6.03/6.23      (((v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_B_1))),
% 6.03/6.23      inference('demod', [status(thm)], ['58', '59'])).
% 6.03/6.23  thf('61', plain,
% 6.03/6.23      (![X45 : $i]:
% 6.03/6.23         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X45))
% 6.03/6.23          | ~ (r2_hidden @ X45 @ sk_C_1)
% 6.03/6.23          | ~ (m1_subset_1 @ X45 @ sk_A))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf('62', plain,
% 6.03/6.23      (((v1_xboole_0 @ sk_B_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | ~ (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 6.03/6.23        | ((sk_E)
% 6.03/6.23            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 6.03/6.23      inference('sup-', [status(thm)], ['60', '61'])).
% 6.03/6.23  thf('63', plain,
% 6.03/6.23      (((v1_xboole_0 @ sk_B_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | ((sk_E)
% 6.03/6.23            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1)))
% 6.03/6.23        | (v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_B_1))),
% 6.03/6.23      inference('sup-', [status(thm)], ['51', '62'])).
% 6.03/6.23  thf('64', plain,
% 6.03/6.23      ((((sk_E)
% 6.03/6.23          != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1)))
% 6.03/6.23        | (v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_B_1))),
% 6.03/6.23      inference('simplify', [status(thm)], ['63'])).
% 6.03/6.23  thf('65', plain,
% 6.03/6.23      ((((sk_E) != (sk_E))
% 6.03/6.23        | (v1_xboole_0 @ sk_C_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_B_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_B_1)
% 6.03/6.23        | (v1_xboole_0 @ sk_A)
% 6.03/6.23        | (v1_xboole_0 @ sk_C_1))),
% 6.03/6.23      inference('sup-', [status(thm)], ['42', '64'])).
% 6.03/6.23  thf('66', plain,
% 6.03/6.23      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 6.03/6.23      inference('simplify', [status(thm)], ['65'])).
% 6.03/6.23  thf('67', plain,
% 6.03/6.23      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf('68', plain,
% 6.03/6.23      (![X28 : $i, X29 : $i, X30 : $i]:
% 6.03/6.23         ((v5_relat_1 @ X28 @ X30)
% 6.03/6.23          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 6.03/6.23      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.03/6.23  thf('69', plain, ((v5_relat_1 @ sk_D_1 @ sk_B_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['67', '68'])).
% 6.03/6.23  thf('70', plain,
% 6.03/6.23      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 6.03/6.23      inference('demod', [status(thm)], ['6', '9'])).
% 6.03/6.23  thf(t172_funct_1, axiom,
% 6.03/6.23    (![A:$i,B:$i]:
% 6.03/6.23     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 6.03/6.23       ( ![C:$i]:
% 6.03/6.23         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 6.03/6.23           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 6.03/6.23  thf('71', plain,
% 6.03/6.23      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.03/6.23         (~ (r2_hidden @ X19 @ (k1_relat_1 @ X20))
% 6.03/6.23          | (r2_hidden @ (k1_funct_1 @ X20 @ X19) @ X21)
% 6.03/6.23          | ~ (v1_funct_1 @ X20)
% 6.03/6.23          | ~ (v5_relat_1 @ X20 @ X21)
% 6.03/6.23          | ~ (v1_relat_1 @ X20))),
% 6.03/6.23      inference('cnf', [status(esa)], [t172_funct_1])).
% 6.03/6.23  thf('72', plain,
% 6.03/6.23      (![X0 : $i]:
% 6.03/6.23         (~ (v1_relat_1 @ sk_D_1)
% 6.03/6.23          | ~ (v5_relat_1 @ sk_D_1 @ X0)
% 6.03/6.23          | ~ (v1_funct_1 @ sk_D_1)
% 6.03/6.23          | (r2_hidden @ 
% 6.03/6.23             (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E)) @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['70', '71'])).
% 6.03/6.23  thf('73', plain, ((v1_relat_1 @ sk_D_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['7', '8'])).
% 6.03/6.23  thf('74', plain, ((v1_funct_1 @ sk_D_1)),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf('75', plain,
% 6.03/6.23      (![X0 : $i]:
% 6.03/6.23         (~ (v5_relat_1 @ sk_D_1 @ X0)
% 6.03/6.23          | (r2_hidden @ 
% 6.03/6.23             (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E)) @ X0))),
% 6.03/6.23      inference('demod', [status(thm)], ['72', '73', '74'])).
% 6.03/6.23  thf('76', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 6.03/6.23      inference('demod', [status(thm)], ['0', '3'])).
% 6.03/6.23  thf('77', plain,
% 6.03/6.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.03/6.23         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 6.03/6.23          | (r2_hidden @ (k4_tarski @ (sk_D @ X18 @ X16 @ X17) @ X17) @ X18)
% 6.03/6.23          | ~ (v1_relat_1 @ X18))),
% 6.03/6.23      inference('cnf', [status(esa)], [t143_relat_1])).
% 6.03/6.23  thf('78', plain,
% 6.03/6.23      ((~ (v1_relat_1 @ sk_D_1)
% 6.03/6.23        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 6.03/6.23           sk_D_1))),
% 6.03/6.23      inference('sup-', [status(thm)], ['76', '77'])).
% 6.03/6.23  thf('79', plain, ((v1_relat_1 @ sk_D_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['7', '8'])).
% 6.03/6.23  thf('80', plain,
% 6.03/6.23      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 6.03/6.23        sk_D_1)),
% 6.03/6.23      inference('demod', [status(thm)], ['78', '79'])).
% 6.03/6.23  thf('81', plain,
% 6.03/6.23      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.03/6.23         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 6.03/6.23          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 6.03/6.23          | ~ (v1_funct_1 @ X23)
% 6.03/6.23          | ~ (v1_relat_1 @ X23))),
% 6.03/6.23      inference('cnf', [status(esa)], [t8_funct_1])).
% 6.03/6.23  thf('82', plain,
% 6.03/6.23      ((~ (v1_relat_1 @ sk_D_1)
% 6.03/6.23        | ~ (v1_funct_1 @ sk_D_1)
% 6.03/6.23        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E))))),
% 6.03/6.23      inference('sup-', [status(thm)], ['80', '81'])).
% 6.03/6.23  thf('83', plain, ((v1_relat_1 @ sk_D_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['7', '8'])).
% 6.03/6.23  thf('84', plain, ((v1_funct_1 @ sk_D_1)),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf('85', plain,
% 6.03/6.23      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E)))),
% 6.03/6.23      inference('demod', [status(thm)], ['82', '83', '84'])).
% 6.03/6.23  thf('86', plain,
% 6.03/6.23      (![X0 : $i]: (~ (v5_relat_1 @ sk_D_1 @ X0) | (r2_hidden @ sk_E @ X0))),
% 6.03/6.23      inference('demod', [status(thm)], ['75', '85'])).
% 6.03/6.23  thf('87', plain, ((r2_hidden @ sk_E @ sk_B_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['69', '86'])).
% 6.03/6.23  thf('88', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.03/6.23  thf('89', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['87', '88'])).
% 6.03/6.23  thf('90', plain, (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_A))),
% 6.03/6.23      inference('clc', [status(thm)], ['66', '89'])).
% 6.03/6.23  thf('91', plain, ((v1_relat_1 @ sk_D_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['7', '8'])).
% 6.03/6.23  thf('92', plain,
% 6.03/6.23      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.03/6.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.03/6.23  thf('93', plain,
% 6.03/6.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.03/6.23         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 6.03/6.23          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ X16)
% 6.03/6.23          | ~ (v1_relat_1 @ X18))),
% 6.03/6.23      inference('cnf', [status(esa)], [t143_relat_1])).
% 6.03/6.23  thf('94', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 6.03/6.23          | ~ (v1_relat_1 @ X1)
% 6.03/6.23          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 6.03/6.23             X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['92', '93'])).
% 6.03/6.23  thf('95', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.03/6.23  thf('96', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         (~ (v1_relat_1 @ X1)
% 6.03/6.23          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 6.03/6.23          | ~ (v1_xboole_0 @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['94', '95'])).
% 6.03/6.23  thf('97', plain,
% 6.03/6.23      (![X4 : $i, X6 : $i]:
% 6.03/6.23         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 6.03/6.23      inference('cnf', [status(esa)], [d3_tarski])).
% 6.03/6.23  thf('98', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.03/6.23  thf('99', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['97', '98'])).
% 6.03/6.23  thf('100', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['97', '98'])).
% 6.03/6.23  thf(d10_xboole_0, axiom,
% 6.03/6.23    (![A:$i,B:$i]:
% 6.03/6.23     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.03/6.23  thf('101', plain,
% 6.03/6.23      (![X7 : $i, X9 : $i]:
% 6.03/6.23         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 6.03/6.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.03/6.23  thf('102', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 6.03/6.23      inference('sup-', [status(thm)], ['100', '101'])).
% 6.03/6.23  thf('103', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['99', '102'])).
% 6.03/6.23  thf('104', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.03/6.23         (~ (v1_xboole_0 @ X0)
% 6.03/6.23          | ~ (v1_relat_1 @ X1)
% 6.03/6.23          | ~ (v1_xboole_0 @ X2)
% 6.03/6.23          | ((k9_relat_1 @ X1 @ X0) = (X2)))),
% 6.03/6.23      inference('sup-', [status(thm)], ['96', '103'])).
% 6.03/6.23  thf('105', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         (((k9_relat_1 @ sk_D_1 @ X0) = (X1))
% 6.03/6.23          | ~ (v1_xboole_0 @ X1)
% 6.03/6.23          | ~ (v1_xboole_0 @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['91', '104'])).
% 6.03/6.23  thf('106', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 6.03/6.23          | ~ (v1_relat_1 @ X1)
% 6.03/6.23          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 6.03/6.23             X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['92', '93'])).
% 6.03/6.23  thf('107', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((r2_hidden @ (sk_D @ sk_D_1 @ X1 @ (sk_B @ X0)) @ X1)
% 6.03/6.23          | ~ (v1_xboole_0 @ X1)
% 6.03/6.23          | ~ (v1_xboole_0 @ X0)
% 6.03/6.23          | ~ (v1_relat_1 @ sk_D_1)
% 6.03/6.23          | (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X1)))),
% 6.03/6.23      inference('sup+', [status(thm)], ['105', '106'])).
% 6.03/6.23  thf('108', plain, ((v1_relat_1 @ sk_D_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['7', '8'])).
% 6.03/6.23  thf('109', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((r2_hidden @ (sk_D @ sk_D_1 @ X1 @ (sk_B @ X0)) @ X1)
% 6.03/6.23          | ~ (v1_xboole_0 @ X1)
% 6.03/6.23          | ~ (v1_xboole_0 @ X0)
% 6.03/6.23          | (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X1)))),
% 6.03/6.23      inference('demod', [status(thm)], ['107', '108'])).
% 6.03/6.23  thf('110', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.03/6.23  thf('111', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0))
% 6.03/6.23          | ~ (v1_xboole_0 @ X1)
% 6.03/6.23          | ~ (v1_xboole_0 @ X0)
% 6.03/6.23          | ~ (v1_xboole_0 @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['109', '110'])).
% 6.03/6.23  thf('112', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]:
% 6.03/6.23         (~ (v1_xboole_0 @ X0)
% 6.03/6.23          | ~ (v1_xboole_0 @ X1)
% 6.03/6.23          | (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 6.03/6.23      inference('simplify', [status(thm)], ['111'])).
% 6.03/6.23  thf('113', plain,
% 6.03/6.23      (![X0 : $i]:
% 6.03/6.23         ((v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 6.03/6.23      inference('condensation', [status(thm)], ['112'])).
% 6.03/6.23  thf('114', plain,
% 6.03/6.23      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 6.03/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.23  thf('115', plain,
% 6.03/6.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.03/6.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.03/6.23  thf('116', plain,
% 6.03/6.23      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 6.03/6.23      inference('sup-', [status(thm)], ['114', '115'])).
% 6.03/6.23  thf('117', plain,
% 6.03/6.23      (![X0 : $i]:
% 6.03/6.23         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 6.03/6.23           = (k9_relat_1 @ sk_D_1 @ X0))),
% 6.03/6.23      inference('sup-', [status(thm)], ['1', '2'])).
% 6.03/6.23  thf('118', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 6.03/6.23      inference('demod', [status(thm)], ['116', '117'])).
% 6.03/6.23  thf('119', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 6.03/6.23      inference('sup-', [status(thm)], ['113', '118'])).
% 6.03/6.23  thf('120', plain, ((v1_xboole_0 @ sk_A)),
% 6.03/6.23      inference('clc', [status(thm)], ['90', '119'])).
% 6.03/6.23  thf('121', plain, ($false), inference('demod', [status(thm)], ['22', '120'])).
% 6.03/6.23  
% 6.03/6.23  % SZS output end Refutation
% 6.03/6.23  
% 6.03/6.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
