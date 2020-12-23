%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kaYmSz4Pss

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:46 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 496 expanded)
%              Number of leaves         :   35 ( 159 expanded)
%              Depth                    :   16
%              Number of atoms          : 1265 (7428 expanded)
%              Number of equality atoms :   28 ( 208 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

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
    r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k9_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ),
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
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X34 @ X32 ) @ X32 )
      | ( ( k1_relset_1 @ X32 @ X33 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('15',plain,
    ( ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
      = sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('24',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X42: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( r2_hidden @ X42 @ ( k7_relset_1 @ X39 @ X40 @ X38 @ X37 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X42 @ X38 @ X39 @ X37 ) @ X42 ) @ X38 )
      | ~ ( m1_subset_1 @ X42 @ X40 )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ X0 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ X0 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_E_1 ) @ sk_D_2 )
    | ~ ( m1_subset_1 @ sk_E_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_E_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_E_1 ) @ sk_D_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','35'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ( X14
        = ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( sk_E_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('40',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X42: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( r2_hidden @ X42 @ ( k7_relset_1 @ X39 @ X40 @ X38 @ X37 ) )
      | ( m1_subset_1 @ ( sk_F @ X42 @ X38 @ X39 @ X37 ) @ X39 )
      | ~ ( m1_subset_1 @ X42 @ X40 )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_E_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['29','34'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X42: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( r2_hidden @ X42 @ ( k7_relset_1 @ X39 @ X40 @ X38 @ X37 ) )
      | ( r2_hidden @ ( sk_F @ X42 @ X38 @ X39 @ X37 ) @ X37 )
      | ~ ( m1_subset_1 @ X42 @ X40 )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_E_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['29','34'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X43: $i] :
      ( ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ X43 ) )
      | ~ ( r2_hidden @ X43 @ sk_C )
      | ~ ( m1_subset_1 @ X43 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_A )
    | ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,
    ( ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('67',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ X9 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['65','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('81',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('82',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('85',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( X14
       != ( k1_funct_1 @ X13 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( k1_funct_1 @ X13 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('91',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('98',plain,
    ( ~ ( v1_xboole_0 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['83','101'])).

thf('103',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = sk_A ),
    inference(demod,[status(thm)],['21','102'])).

thf('104',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['83','101'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['12','103','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kaYmSz4Pss
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 294 iterations in 0.153s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.60  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.41/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.60  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.41/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.41/0.60  thf(t116_funct_2, conjecture,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60       ( ![E:$i]:
% 0.41/0.60         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.41/0.60              ( ![F:$i]:
% 0.41/0.60                ( ( m1_subset_1 @ F @ A ) =>
% 0.41/0.60                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.41/0.60                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.60            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60          ( ![E:$i]:
% 0.41/0.60            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.41/0.60                 ( ![F:$i]:
% 0.41/0.60                   ( ( m1_subset_1 @ F @ A ) =>
% 0.41/0.60                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.41/0.60                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(redefinition_k7_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.41/0.60          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.41/0.60           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('4', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.41/0.60  thf(t143_relat_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ C ) =>
% 0.41/0.60       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.41/0.60         ( ?[D:$i]:
% 0.41/0.60           ( ( r2_hidden @ D @ B ) & 
% 0.41/0.60             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.41/0.60             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.41/0.60          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ (k1_relat_1 @ X11))
% 0.41/0.60          | ~ (v1_relat_1 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      ((~ (v1_relat_1 @ sk_D_2)
% 0.41/0.60        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(cc1_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( v1_relat_1 @ C ) ))).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.60         ((v1_relat_1 @ X15)
% 0.41/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.60  thf('9', plain, ((v1_relat_1 @ sk_D_2)),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2))),
% 0.41/0.60      inference('demod', [status(thm)], ['6', '9'])).
% 0.41/0.60  thf(d1_xboole_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('12', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t22_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.41/0.60       ( ( ![D:$i]:
% 0.41/0.60           ( ~( ( r2_hidden @ D @ B ) & 
% 0.41/0.60                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.41/0.60         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D_1 @ X34 @ X32) @ X32)
% 0.41/0.60          | ((k1_relset_1 @ X32 @ X33 @ X34) = (X32))
% 0.41/0.60          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.41/0.60      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      ((((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (sk_A))
% 0.41/0.60        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_A) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.60         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.41/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      ((((k1_relat_1 @ sk_D_2) = (sk_A))
% 0.41/0.60        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_A) @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['15', '18'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      ((((k1_relat_1 @ sk_D_2) = (sk_A)) | ~ (v1_xboole_0 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf('22', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t52_relset_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.41/0.60               ( ![D:$i]:
% 0.41/0.60                 ( ( m1_subset_1 @
% 0.41/0.60                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.41/0.60                   ( ![E:$i]:
% 0.41/0.60                     ( ( m1_subset_1 @ E @ A ) =>
% 0.41/0.60                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.41/0.60                         ( ?[F:$i]:
% 0.41/0.60                           ( ( r2_hidden @ F @ B ) & 
% 0.41/0.60                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.41/0.60                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ X37)
% 0.41/0.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.41/0.60          | ~ (r2_hidden @ X42 @ (k7_relset_1 @ X39 @ X40 @ X38 @ X37))
% 0.41/0.60          | (r2_hidden @ (k4_tarski @ (sk_F @ X42 @ X38 @ X39 @ X37) @ X42) @ 
% 0.41/0.60             X38)
% 0.41/0.60          | ~ (m1_subset_1 @ X42 @ X40)
% 0.41/0.60          | (v1_xboole_0 @ X39)
% 0.41/0.60          | (v1_xboole_0 @ X40))),
% 0.41/0.60      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.41/0.60          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X0) @ 
% 0.41/0.60             sk_D_2)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1))
% 0.41/0.60          | (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.41/0.60           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.41/0.60          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X0) @ 
% 0.41/0.60             sk_D_2)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_2 @ X1))
% 0.41/0.60          | (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('demod', [status(thm)], ['25', '26'])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_C)
% 0.41/0.60        | (r2_hidden @ 
% 0.41/0.60           (k4_tarski @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_E_1) @ 
% 0.41/0.60           sk_D_2)
% 0.41/0.60        | ~ (m1_subset_1 @ sk_E_1 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['22', '27'])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_k7_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.41/0.60          | (m1_subset_1 @ (k7_relset_1 @ X22 @ X23 @ X21 @ X24) @ 
% 0.41/0.60             (k1_zfmisc_1 @ X23)))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0) @ 
% 0.41/0.60          (k1_zfmisc_1 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.60  thf(t4_subset, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.41/0.60       ( m1_subset_1 @ A @ C ) ))).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X5 @ X6)
% 0.41/0.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.41/0.60          | (m1_subset_1 @ X5 @ X7))),
% 0.41/0.60      inference('cnf', [status(esa)], [t4_subset])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((m1_subset_1 @ X1 @ sk_B_1)
% 0.41/0.60          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.60  thf('35', plain, ((m1_subset_1 @ sk_E_1 @ sk_B_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '34'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_C)
% 0.41/0.60        | (r2_hidden @ 
% 0.41/0.60           (k4_tarski @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_E_1) @ 
% 0.41/0.60           sk_D_2)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['28', '35'])).
% 0.41/0.60  thf(t8_funct_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.60       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.41/0.60         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.41/0.60           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.60         (~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ X13)
% 0.41/0.60          | ((X14) = (k1_funct_1 @ X13 @ X12))
% 0.41/0.60          | ~ (v1_funct_1 @ X13)
% 0.41/0.60          | ~ (v1_relat_1 @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_C)
% 0.41/0.60        | ~ (v1_relat_1 @ sk_D_2)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_D_2)
% 0.41/0.60        | ((sk_E_1)
% 0.41/0.60            = (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.60  thf('39', plain, ((v1_relat_1 @ sk_D_2)),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('40', plain, ((v1_funct_1 @ sk_D_2)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_C)
% 0.41/0.60        | ((sk_E_1)
% 0.41/0.60            = (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C))))),
% 0.41/0.60      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.41/0.60  thf('42', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ X37)
% 0.41/0.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.41/0.60          | ~ (r2_hidden @ X42 @ (k7_relset_1 @ X39 @ X40 @ X38 @ X37))
% 0.41/0.60          | (m1_subset_1 @ (sk_F @ X42 @ X38 @ X39 @ X37) @ X39)
% 0.41/0.60          | ~ (m1_subset_1 @ X42 @ X40)
% 0.41/0.60          | (v1_xboole_0 @ X39)
% 0.41/0.60          | (v1_xboole_0 @ X40))),
% 0.41/0.60      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.41/0.60          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ sk_A)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1))
% 0.41/0.60          | (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.41/0.60           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.41/0.60          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ sk_A)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_2 @ X1))
% 0.41/0.60          | (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_C)
% 0.41/0.60        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_A)
% 0.41/0.60        | ~ (m1_subset_1 @ sk_E_1 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['42', '47'])).
% 0.41/0.60  thf('49', plain, ((m1_subset_1 @ sk_E_1 @ sk_B_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '34'])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_C)
% 0.41/0.60        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['48', '49'])).
% 0.41/0.60  thf('51', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ X37)
% 0.41/0.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.41/0.60          | ~ (r2_hidden @ X42 @ (k7_relset_1 @ X39 @ X40 @ X38 @ X37))
% 0.41/0.60          | (r2_hidden @ (sk_F @ X42 @ X38 @ X39 @ X37) @ X37)
% 0.41/0.60          | ~ (m1_subset_1 @ X42 @ X40)
% 0.41/0.60          | (v1_xboole_0 @ X39)
% 0.41/0.60          | (v1_xboole_0 @ X40))),
% 0.41/0.60      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.41/0.60  thf('54', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.41/0.60          | (r2_hidden @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X1)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1))
% 0.41/0.60          | (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.41/0.60           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.41/0.60          | (r2_hidden @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X1)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_2 @ X1))
% 0.41/0.60          | (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('demod', [status(thm)], ['54', '55'])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_C)
% 0.41/0.60        | (r2_hidden @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_C)
% 0.41/0.60        | ~ (m1_subset_1 @ sk_E_1 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['51', '56'])).
% 0.41/0.60  thf('58', plain, ((m1_subset_1 @ sk_E_1 @ sk_B_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '34'])).
% 0.41/0.60  thf('59', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_C)
% 0.41/0.60        | (r2_hidden @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_C)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['57', '58'])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      (![X43 : $i]:
% 0.41/0.60         (((sk_E_1) != (k1_funct_1 @ sk_D_2 @ X43))
% 0.41/0.60          | ~ (r2_hidden @ X43 @ sk_C)
% 0.41/0.60          | ~ (m1_subset_1 @ X43 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_C)
% 0.41/0.60        | ~ (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_A)
% 0.41/0.60        | ((sk_E_1)
% 0.41/0.60            != (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['59', '60'])).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_C)
% 0.41/0.60        | ((sk_E_1)
% 0.41/0.60            != (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C)))
% 0.41/0.60        | (v1_xboole_0 @ sk_C)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['50', '61'])).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      ((((sk_E_1)
% 0.41/0.60          != (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C)))
% 0.41/0.60        | (v1_xboole_0 @ sk_C)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('simplify', [status(thm)], ['62'])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      ((((sk_E_1) != (sk_E_1))
% 0.41/0.60        | (v1_xboole_0 @ sk_C)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '63'])).
% 0.41/0.60  thf('65', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['64'])).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.41/0.60          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ X9)
% 0.41/0.60          | ~ (v1_relat_1 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.41/0.60  thf('68', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X1)
% 0.41/0.60          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.41/0.60             X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['66', '67'])).
% 0.41/0.60  thf('69', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('70', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X1)
% 0.41/0.60          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['68', '69'])).
% 0.41/0.60  thf('71', plain,
% 0.41/0.60      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('72', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('73', plain,
% 0.41/0.60      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['71', '72'])).
% 0.41/0.60  thf('74', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.41/0.60           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('75', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['73', '74'])).
% 0.41/0.60  thf('76', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_D_2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['70', '75'])).
% 0.41/0.60  thf('77', plain, ((v1_relat_1 @ sk_D_2)),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('78', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.41/0.60      inference('demod', [status(thm)], ['76', '77'])).
% 0.41/0.60  thf('79', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('clc', [status(thm)], ['65', '78'])).
% 0.41/0.60  thf('80', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(cc4_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( v1_xboole_0 @ A ) =>
% 0.41/0.60       ( ![C:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.41/0.60           ( v1_xboole_0 @ C ) ) ) ))).
% 0.41/0.60  thf('81', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X18)
% 0.41/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 0.41/0.60          | (v1_xboole_0 @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.41/0.60  thf('82', plain, (((v1_xboole_0 @ sk_D_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['80', '81'])).
% 0.41/0.60  thf('83', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D_2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['79', '82'])).
% 0.41/0.60  thf('84', plain,
% 0.41/0.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('85', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.41/0.60          | ((X14) != (k1_funct_1 @ X13 @ X12))
% 0.41/0.60          | (r2_hidden @ (k4_tarski @ X12 @ X14) @ X13)
% 0.41/0.60          | ~ (v1_funct_1 @ X13)
% 0.41/0.60          | ~ (v1_relat_1 @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.41/0.60  thf('86', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X13)
% 0.41/0.60          | ~ (v1_funct_1 @ X13)
% 0.41/0.60          | (r2_hidden @ (k4_tarski @ X12 @ (k1_funct_1 @ X13 @ X12)) @ X13)
% 0.41/0.60          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X13)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['85'])).
% 0.41/0.60  thf('87', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.41/0.60              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 0.41/0.60             X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['84', '86'])).
% 0.41/0.60  thf('88', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('89', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['87', '88'])).
% 0.41/0.60  thf('90', plain,
% 0.41/0.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('91', plain,
% 0.41/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.41/0.60          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ (k1_relat_1 @ X11))
% 0.41/0.60          | ~ (v1_relat_1 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.41/0.60  thf('92', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X1)
% 0.41/0.60          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.41/0.60             (k1_relat_1 @ X1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['90', '91'])).
% 0.41/0.60  thf('93', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('94', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X0)
% 0.41/0.60          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.41/0.60          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['92', '93'])).
% 0.41/0.60  thf('95', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.41/0.60          | ~ (v1_relat_1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['89', '94'])).
% 0.41/0.60  thf('96', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['95'])).
% 0.41/0.60  thf('97', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['73', '74'])).
% 0.41/0.60  thf('98', plain,
% 0.41/0.60      ((~ (v1_xboole_0 @ sk_D_2)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_D_2)
% 0.41/0.60        | ~ (v1_relat_1 @ sk_D_2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['96', '97'])).
% 0.41/0.60  thf('99', plain, ((v1_funct_1 @ sk_D_2)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('100', plain, ((v1_relat_1 @ sk_D_2)),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('101', plain, (~ (v1_xboole_0 @ sk_D_2)),
% 0.41/0.60      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.41/0.60  thf('102', plain, ((v1_xboole_0 @ sk_A)),
% 0.41/0.60      inference('clc', [status(thm)], ['83', '101'])).
% 0.41/0.60  thf('103', plain, (((k1_relat_1 @ sk_D_2) = (sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['21', '102'])).
% 0.41/0.60  thf('104', plain, ((v1_xboole_0 @ sk_A)),
% 0.41/0.60      inference('clc', [status(thm)], ['83', '101'])).
% 0.41/0.60  thf('105', plain, ($false),
% 0.41/0.60      inference('demod', [status(thm)], ['12', '103', '104'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
