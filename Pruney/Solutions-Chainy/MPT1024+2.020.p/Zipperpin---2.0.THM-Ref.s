%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0w4dPc1mYm

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:36 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 504 expanded)
%              Number of leaves         :   36 ( 161 expanded)
%              Depth                    :   18
%              Number of atoms          : 1309 (7516 expanded)
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
      | ( r2_hidden @ ( sk_F @ X42 @ X38 @ X39 @ X37 ) @ X37 )
      | ~ ( m1_subset_1 @ X42 @ X40 )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ X1 )
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
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_E_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_E_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['29','34'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_C )
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
      | ( m1_subset_1 @ ( sk_F @ X42 @ X38 @ X39 @ X37 ) @ X39 )
      | ~ ( m1_subset_1 @ X42 @ X40 )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ sk_A )
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
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['29','34'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_A )
      | ~ ( r2_hidden @ X43 @ sk_C )
      | ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) )
    | ~ ( r2_hidden @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','64'])).

thf('66',plain,
    ( ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('70',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ X9 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['68','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('84',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('88',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( X14
       != ( k1_funct_1 @ X13 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('89',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( k1_funct_1 @ X13 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('94',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['86','104'])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = sk_A ),
    inference(demod,[status(thm)],['21','105'])).

thf('107',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['86','104'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['12','106','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0w4dPc1mYm
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.61  % Solved by: fo/fo7.sh
% 0.36/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.61  % done 306 iterations in 0.153s
% 0.36/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.61  % SZS output start Refutation
% 0.36/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.61  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.36/0.61  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.61  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.36/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.36/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.61  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.61  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.36/0.61  thf(t115_funct_2, conjecture,
% 0.36/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.61       ( ![E:$i]:
% 0.36/0.61         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.36/0.61              ( ![F:$i]:
% 0.36/0.61                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.36/0.61                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.61            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.61          ( ![E:$i]:
% 0.36/0.61            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.36/0.61                 ( ![F:$i]:
% 0.36/0.61                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.36/0.61                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.36/0.61    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.36/0.61  thf('0', plain,
% 0.36/0.61      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('1', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(redefinition_k7_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.36/0.61  thf('2', plain,
% 0.36/0.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.36/0.61          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.36/0.61  thf('3', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.36/0.61           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.61  thf('4', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.36/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.61  thf(t143_relat_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( v1_relat_1 @ C ) =>
% 0.36/0.61       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.36/0.61         ( ?[D:$i]:
% 0.36/0.61           ( ( r2_hidden @ D @ B ) & 
% 0.36/0.61             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.36/0.61             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.36/0.61  thf('5', plain,
% 0.36/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.36/0.61          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ (k1_relat_1 @ X11))
% 0.36/0.61          | ~ (v1_relat_1 @ X11))),
% 0.36/0.61      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.36/0.61  thf('6', plain,
% 0.36/0.61      ((~ (v1_relat_1 @ sk_D_2)
% 0.36/0.61        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.61  thf('7', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(cc1_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( v1_relat_1 @ C ) ))).
% 0.36/0.61  thf('8', plain,
% 0.36/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.61         ((v1_relat_1 @ X15)
% 0.36/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.36/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.61  thf('9', plain, ((v1_relat_1 @ sk_D_2)),
% 0.36/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.61  thf('10', plain,
% 0.36/0.61      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2))),
% 0.36/0.61      inference('demod', [status(thm)], ['6', '9'])).
% 0.36/0.61  thf(d1_xboole_0, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.61  thf('11', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.61  thf('12', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_2))),
% 0.36/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.61  thf('13', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t22_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.61       ( ( ![D:$i]:
% 0.36/0.61           ( ~( ( r2_hidden @ D @ B ) & 
% 0.36/0.61                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.36/0.61         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.36/0.61  thf('14', plain,
% 0.36/0.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.61         ((r2_hidden @ (sk_D_1 @ X34 @ X32) @ X32)
% 0.36/0.61          | ((k1_relset_1 @ X32 @ X33 @ X34) = (X32))
% 0.36/0.61          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.36/0.61      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.36/0.61  thf('15', plain,
% 0.36/0.61      ((((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (sk_A))
% 0.36/0.61        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_A) @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.61  thf('16', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.61  thf('17', plain,
% 0.36/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.61         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.36/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.61  thf('18', plain,
% 0.36/0.61      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.36/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.61  thf('19', plain,
% 0.36/0.61      ((((k1_relat_1 @ sk_D_2) = (sk_A))
% 0.36/0.61        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_A) @ sk_A))),
% 0.36/0.61      inference('demod', [status(thm)], ['15', '18'])).
% 0.36/0.61  thf('20', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.61  thf('21', plain,
% 0.36/0.61      ((((k1_relat_1 @ sk_D_2) = (sk_A)) | ~ (v1_xboole_0 @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.61  thf('22', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.36/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.61  thf('23', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t52_relset_1, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.61           ( ![C:$i]:
% 0.36/0.61             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.36/0.61               ( ![D:$i]:
% 0.36/0.61                 ( ( m1_subset_1 @
% 0.36/0.61                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.36/0.61                   ( ![E:$i]:
% 0.36/0.61                     ( ( m1_subset_1 @ E @ A ) =>
% 0.36/0.61                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.36/0.61                         ( ?[F:$i]:
% 0.36/0.61                           ( ( r2_hidden @ F @ B ) & 
% 0.36/0.61                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.36/0.61                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.61  thf('24', plain,
% 0.36/0.61      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ X37)
% 0.36/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.36/0.61          | ~ (r2_hidden @ X42 @ (k7_relset_1 @ X39 @ X40 @ X38 @ X37))
% 0.36/0.61          | (r2_hidden @ (k4_tarski @ (sk_F @ X42 @ X38 @ X39 @ X37) @ X42) @ 
% 0.36/0.61             X38)
% 0.36/0.61          | ~ (m1_subset_1 @ X42 @ X40)
% 0.36/0.61          | (v1_xboole_0 @ X39)
% 0.36/0.61          | (v1_xboole_0 @ X40))),
% 0.36/0.61      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.36/0.61  thf('25', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ sk_A)
% 0.36/0.61          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.36/0.61          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X0) @ 
% 0.36/0.61             sk_D_2)
% 0.36/0.61          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1))
% 0.36/0.61          | (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.61  thf('26', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.36/0.61           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.61  thf('27', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ sk_A)
% 0.36/0.61          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.36/0.61          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X0) @ 
% 0.36/0.61             sk_D_2)
% 0.36/0.61          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_2 @ X1))
% 0.36/0.61          | (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('demod', [status(thm)], ['25', '26'])).
% 0.36/0.61  thf('28', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_C)
% 0.36/0.61        | (r2_hidden @ 
% 0.36/0.61           (k4_tarski @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_E_1) @ 
% 0.36/0.61           sk_D_2)
% 0.36/0.61        | ~ (m1_subset_1 @ sk_E_1 @ sk_B_1)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['22', '27'])).
% 0.36/0.61  thf('29', plain,
% 0.36/0.61      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('30', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(dt_k7_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.36/0.61  thf('31', plain,
% 0.36/0.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.36/0.61          | (m1_subset_1 @ (k7_relset_1 @ X22 @ X23 @ X21 @ X24) @ 
% 0.36/0.61             (k1_zfmisc_1 @ X23)))),
% 0.36/0.61      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.36/0.61  thf('32', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0) @ 
% 0.36/0.61          (k1_zfmisc_1 @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.61  thf(t4_subset, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.36/0.61       ( m1_subset_1 @ A @ C ) ))).
% 0.36/0.61  thf('33', plain,
% 0.36/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X5 @ X6)
% 0.36/0.61          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.36/0.61          | (m1_subset_1 @ X5 @ X7))),
% 0.36/0.61      inference('cnf', [status(esa)], [t4_subset])).
% 0.36/0.61  thf('34', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((m1_subset_1 @ X1 @ sk_B_1)
% 0.36/0.61          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.61  thf('35', plain, ((m1_subset_1 @ sk_E_1 @ sk_B_1)),
% 0.36/0.61      inference('sup-', [status(thm)], ['29', '34'])).
% 0.36/0.61  thf('36', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_C)
% 0.36/0.61        | (r2_hidden @ 
% 0.36/0.61           (k4_tarski @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_E_1) @ 
% 0.36/0.61           sk_D_2)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('demod', [status(thm)], ['28', '35'])).
% 0.36/0.61  thf(t8_funct_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.61       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.36/0.61         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.36/0.61           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.36/0.61  thf('37', plain,
% 0.36/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.61         (~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ X13)
% 0.36/0.61          | ((X14) = (k1_funct_1 @ X13 @ X12))
% 0.36/0.61          | ~ (v1_funct_1 @ X13)
% 0.36/0.61          | ~ (v1_relat_1 @ X13))),
% 0.36/0.61      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.36/0.61  thf('38', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_C)
% 0.36/0.61        | ~ (v1_relat_1 @ sk_D_2)
% 0.36/0.61        | ~ (v1_funct_1 @ sk_D_2)
% 0.36/0.61        | ((sk_E_1)
% 0.36/0.61            = (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.61  thf('39', plain, ((v1_relat_1 @ sk_D_2)),
% 0.36/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.61  thf('40', plain, ((v1_funct_1 @ sk_D_2)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('41', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_C)
% 0.36/0.61        | ((sk_E_1)
% 0.36/0.61            = (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C))))),
% 0.36/0.61      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.36/0.61  thf('42', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.36/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.61  thf('43', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('44', plain,
% 0.36/0.61      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ X37)
% 0.36/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.36/0.61          | ~ (r2_hidden @ X42 @ (k7_relset_1 @ X39 @ X40 @ X38 @ X37))
% 0.36/0.61          | (r2_hidden @ (sk_F @ X42 @ X38 @ X39 @ X37) @ X37)
% 0.36/0.61          | ~ (m1_subset_1 @ X42 @ X40)
% 0.36/0.61          | (v1_xboole_0 @ X39)
% 0.36/0.61          | (v1_xboole_0 @ X40))),
% 0.36/0.61      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.36/0.61  thf('45', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ sk_A)
% 0.36/0.61          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.36/0.61          | (r2_hidden @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X1)
% 0.36/0.61          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1))
% 0.36/0.61          | (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.61  thf('46', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.36/0.61           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.61  thf('47', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ sk_A)
% 0.36/0.61          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.36/0.61          | (r2_hidden @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X1)
% 0.36/0.61          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_2 @ X1))
% 0.36/0.61          | (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.36/0.61  thf('48', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_C)
% 0.36/0.61        | (r2_hidden @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_C)
% 0.36/0.61        | ~ (m1_subset_1 @ sk_E_1 @ sk_B_1)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['42', '47'])).
% 0.36/0.61  thf('49', plain, ((m1_subset_1 @ sk_E_1 @ sk_B_1)),
% 0.36/0.61      inference('sup-', [status(thm)], ['29', '34'])).
% 0.36/0.61  thf('50', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_C)
% 0.36/0.61        | (r2_hidden @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_C)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.36/0.61  thf('51', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.36/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.61  thf('52', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('53', plain,
% 0.36/0.61      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ X37)
% 0.36/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.36/0.61          | ~ (r2_hidden @ X42 @ (k7_relset_1 @ X39 @ X40 @ X38 @ X37))
% 0.36/0.61          | (m1_subset_1 @ (sk_F @ X42 @ X38 @ X39 @ X37) @ X39)
% 0.36/0.61          | ~ (m1_subset_1 @ X42 @ X40)
% 0.36/0.61          | (v1_xboole_0 @ X39)
% 0.36/0.61          | (v1_xboole_0 @ X40))),
% 0.36/0.61      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.36/0.61  thf('54', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ sk_A)
% 0.36/0.61          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.36/0.61          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ sk_A)
% 0.36/0.61          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1))
% 0.36/0.61          | (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.61  thf('55', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.36/0.61           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.61  thf('56', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ sk_A)
% 0.36/0.61          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.36/0.61          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ sk_A)
% 0.36/0.61          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_2 @ X1))
% 0.36/0.61          | (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.61  thf('57', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_C)
% 0.36/0.61        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_A)
% 0.36/0.61        | ~ (m1_subset_1 @ sk_E_1 @ sk_B_1)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['51', '56'])).
% 0.36/0.61  thf('58', plain, ((m1_subset_1 @ sk_E_1 @ sk_B_1)),
% 0.36/0.61      inference('sup-', [status(thm)], ['29', '34'])).
% 0.36/0.61  thf('59', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_C)
% 0.36/0.61        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.61  thf(t2_subset, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.61       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.61  thf('60', plain,
% 0.36/0.61      (![X3 : $i, X4 : $i]:
% 0.36/0.61         ((r2_hidden @ X3 @ X4)
% 0.36/0.61          | (v1_xboole_0 @ X4)
% 0.36/0.61          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.36/0.61      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.61  thf('61', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_C)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (r2_hidden @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['59', '60'])).
% 0.36/0.61  thf('62', plain,
% 0.36/0.61      (((r2_hidden @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_C)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('simplify', [status(thm)], ['61'])).
% 0.36/0.61  thf('63', plain,
% 0.36/0.61      (![X43 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X43 @ sk_A)
% 0.36/0.61          | ~ (r2_hidden @ X43 @ sk_C)
% 0.36/0.61          | ((sk_E_1) != (k1_funct_1 @ sk_D_2 @ X43)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('64', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_C)
% 0.36/0.61        | ((sk_E_1)
% 0.36/0.61            != (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C)))
% 0.36/0.61        | ~ (r2_hidden @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_C))),
% 0.36/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.36/0.61  thf('65', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_C)
% 0.36/0.61        | ((sk_E_1)
% 0.36/0.61            != (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C)))
% 0.36/0.61        | (v1_xboole_0 @ sk_C)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['50', '64'])).
% 0.36/0.61  thf('66', plain,
% 0.36/0.61      ((((sk_E_1)
% 0.36/0.61          != (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C)))
% 0.36/0.61        | (v1_xboole_0 @ sk_C)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('simplify', [status(thm)], ['65'])).
% 0.36/0.61  thf('67', plain,
% 0.36/0.61      ((((sk_E_1) != (sk_E_1))
% 0.36/0.61        | (v1_xboole_0 @ sk_C)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1)
% 0.36/0.61        | (v1_xboole_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_C))),
% 0.36/0.61      inference('sup-', [status(thm)], ['41', '66'])).
% 0.36/0.61  thf('68', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 0.36/0.61      inference('simplify', [status(thm)], ['67'])).
% 0.36/0.61  thf('69', plain,
% 0.36/0.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.61  thf('70', plain,
% 0.36/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.36/0.61          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ X9)
% 0.36/0.61          | ~ (v1_relat_1 @ X11))),
% 0.36/0.61      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.36/0.61  thf('71', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.36/0.61          | ~ (v1_relat_1 @ X1)
% 0.36/0.61          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.36/0.61             X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.61  thf('72', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.61  thf('73', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (~ (v1_relat_1 @ X1)
% 0.36/0.61          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.36/0.61          | ~ (v1_xboole_0 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.36/0.61  thf('74', plain,
% 0.36/0.61      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('75', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.61  thf('76', plain,
% 0.36/0.61      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.36/0.61      inference('sup-', [status(thm)], ['74', '75'])).
% 0.36/0.61  thf('77', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.36/0.61           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.61  thf('78', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.36/0.61      inference('demod', [status(thm)], ['76', '77'])).
% 0.36/0.61  thf('79', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_D_2))),
% 0.36/0.61      inference('sup-', [status(thm)], ['73', '78'])).
% 0.36/0.61  thf('80', plain, ((v1_relat_1 @ sk_D_2)),
% 0.36/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.61  thf('81', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.36/0.61      inference('demod', [status(thm)], ['79', '80'])).
% 0.36/0.61  thf('82', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('clc', [status(thm)], ['68', '81'])).
% 0.36/0.61  thf('83', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(cc4_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.61       ( ![C:$i]:
% 0.36/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.61           ( v1_xboole_0 @ C ) ) ) ))).
% 0.36/0.61  thf('84', plain,
% 0.36/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.61         (~ (v1_xboole_0 @ X18)
% 0.36/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 0.36/0.61          | (v1_xboole_0 @ X19))),
% 0.36/0.61      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.36/0.61  thf('85', plain, (((v1_xboole_0 @ sk_D_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['83', '84'])).
% 0.36/0.61  thf('86', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D_2))),
% 0.36/0.61      inference('sup-', [status(thm)], ['82', '85'])).
% 0.36/0.61  thf('87', plain,
% 0.36/0.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.61  thf('88', plain,
% 0.36/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.36/0.61          | ((X14) != (k1_funct_1 @ X13 @ X12))
% 0.36/0.61          | (r2_hidden @ (k4_tarski @ X12 @ X14) @ X13)
% 0.36/0.61          | ~ (v1_funct_1 @ X13)
% 0.36/0.61          | ~ (v1_relat_1 @ X13))),
% 0.36/0.61      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.36/0.61  thf('89', plain,
% 0.36/0.61      (![X12 : $i, X13 : $i]:
% 0.36/0.61         (~ (v1_relat_1 @ X13)
% 0.36/0.61          | ~ (v1_funct_1 @ X13)
% 0.36/0.61          | (r2_hidden @ (k4_tarski @ X12 @ (k1_funct_1 @ X13 @ X12)) @ X13)
% 0.36/0.61          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X13)))),
% 0.36/0.61      inference('simplify', [status(thm)], ['88'])).
% 0.36/0.61  thf('90', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.36/0.61          | (r2_hidden @ 
% 0.36/0.61             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.36/0.61              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 0.36/0.61             X0)
% 0.36/0.61          | ~ (v1_funct_1 @ X0)
% 0.36/0.61          | ~ (v1_relat_1 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['87', '89'])).
% 0.36/0.61  thf('91', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.61  thf('92', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (~ (v1_relat_1 @ X0)
% 0.36/0.61          | ~ (v1_funct_1 @ X0)
% 0.36/0.61          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.36/0.61          | ~ (v1_xboole_0 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['90', '91'])).
% 0.36/0.61  thf('93', plain,
% 0.36/0.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.61  thf('94', plain,
% 0.36/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.36/0.61          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ (k1_relat_1 @ X11))
% 0.36/0.61          | ~ (v1_relat_1 @ X11))),
% 0.36/0.61      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.36/0.61  thf('95', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.36/0.61          | ~ (v1_relat_1 @ X1)
% 0.36/0.61          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.36/0.61             (k1_relat_1 @ X1)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['93', '94'])).
% 0.36/0.61  thf('96', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.61  thf('97', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (~ (v1_relat_1 @ X0)
% 0.36/0.61          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.36/0.61          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['95', '96'])).
% 0.36/0.61  thf('98', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (~ (v1_xboole_0 @ X0)
% 0.36/0.61          | ~ (v1_funct_1 @ X0)
% 0.36/0.61          | ~ (v1_relat_1 @ X0)
% 0.36/0.61          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.36/0.61          | ~ (v1_relat_1 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['92', '97'])).
% 0.36/0.61  thf('99', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.36/0.61          | ~ (v1_relat_1 @ X0)
% 0.36/0.61          | ~ (v1_funct_1 @ X0)
% 0.36/0.61          | ~ (v1_xboole_0 @ X0))),
% 0.36/0.61      inference('simplify', [status(thm)], ['98'])).
% 0.36/0.61  thf('100', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.36/0.61      inference('demod', [status(thm)], ['76', '77'])).
% 0.36/0.61  thf('101', plain,
% 0.36/0.61      ((~ (v1_xboole_0 @ sk_D_2)
% 0.36/0.61        | ~ (v1_funct_1 @ sk_D_2)
% 0.36/0.61        | ~ (v1_relat_1 @ sk_D_2))),
% 0.36/0.61      inference('sup-', [status(thm)], ['99', '100'])).
% 0.36/0.61  thf('102', plain, ((v1_funct_1 @ sk_D_2)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('103', plain, ((v1_relat_1 @ sk_D_2)),
% 0.36/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.61  thf('104', plain, (~ (v1_xboole_0 @ sk_D_2)),
% 0.36/0.61      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.36/0.61  thf('105', plain, ((v1_xboole_0 @ sk_A)),
% 0.36/0.61      inference('clc', [status(thm)], ['86', '104'])).
% 0.36/0.61  thf('106', plain, (((k1_relat_1 @ sk_D_2) = (sk_A))),
% 0.36/0.61      inference('demod', [status(thm)], ['21', '105'])).
% 0.36/0.61  thf('107', plain, ((v1_xboole_0 @ sk_A)),
% 0.36/0.61      inference('clc', [status(thm)], ['86', '104'])).
% 0.36/0.61  thf('108', plain, ($false),
% 0.36/0.61      inference('demod', [status(thm)], ['12', '106', '107'])).
% 0.36/0.61  
% 0.36/0.61  % SZS output end Refutation
% 0.36/0.61  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
