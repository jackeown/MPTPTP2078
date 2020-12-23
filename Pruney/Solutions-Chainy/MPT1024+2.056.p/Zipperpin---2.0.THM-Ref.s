%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AKJQIL5qbt

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:42 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 894 expanded)
%              Number of leaves         :   40 ( 282 expanded)
%              Depth                    :   17
%              Number of atoms          :  829 (12230 expanded)
%              Number of equality atoms :   59 ( 505 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

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
    r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
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
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('16',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X26 @ X24 ) @ X24 )
      | ( ( k1_relset_1 @ X24 @ X25 @ X26 )
        = X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('17',plain,
    ( ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
      = sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = sk_A )
    | ~ ( r1_tarski @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_A )
      | ~ ( r2_hidden @ X37 @ sk_C )
      | ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['42','43'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ( X14
        = ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( sk_E_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('48',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( sk_E_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ X9 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('54',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_1 != sk_E_1 ) ),
    inference(demod,[status(thm)],['39','49','54'])).

thf('56',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','56'])).

thf('58',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 != k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('63',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['42','43'])).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('67',plain,(
    ~ ( r1_tarski @ sk_D_2 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69'])).

thf('72',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('74',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['23','70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['14','74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AKJQIL5qbt
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:38:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.58/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.76  % Solved by: fo/fo7.sh
% 0.58/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.76  % done 294 iterations in 0.311s
% 0.58/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.76  % SZS output start Refutation
% 0.58/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.76  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.58/0.76  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.58/0.76  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.58/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.58/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.76  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.58/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.76  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.58/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.76  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.58/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.76  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.58/0.76  thf(t115_funct_2, conjecture,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.76       ( ![E:$i]:
% 0.58/0.76         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.58/0.76              ( ![F:$i]:
% 0.58/0.76                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.58/0.76                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.76    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.76            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.76          ( ![E:$i]:
% 0.58/0.76            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.58/0.76                 ( ![F:$i]:
% 0.58/0.76                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.58/0.76                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.58/0.76    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.58/0.76  thf('0', plain,
% 0.58/0.76      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('1', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(redefinition_k7_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.58/0.76  thf('2', plain,
% 0.58/0.76      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.58/0.76          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.58/0.76      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.58/0.76  thf('3', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 0.58/0.76           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.76  thf('4', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.76  thf(t143_relat_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( v1_relat_1 @ C ) =>
% 0.58/0.76       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.58/0.76         ( ?[D:$i]:
% 0.58/0.76           ( ( r2_hidden @ D @ B ) & 
% 0.58/0.76             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.58/0.76             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.58/0.76  thf('5', plain,
% 0.58/0.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.58/0.76          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ (k1_relat_1 @ X11))
% 0.58/0.76          | ~ (v1_relat_1 @ X11))),
% 0.58/0.76      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.58/0.76  thf('6', plain,
% 0.58/0.76      ((~ (v1_relat_1 @ sk_D_2)
% 0.58/0.76        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.76  thf('7', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(cc2_relat_1, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( v1_relat_1 @ A ) =>
% 0.58/0.76       ( ![B:$i]:
% 0.58/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.58/0.76  thf('8', plain,
% 0.58/0.76      (![X4 : $i, X5 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.58/0.76          | (v1_relat_1 @ X4)
% 0.58/0.76          | ~ (v1_relat_1 @ X5))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.58/0.76  thf('9', plain,
% 0.58/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_2))),
% 0.58/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.76  thf(fc6_relat_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.58/0.76  thf('10', plain,
% 0.58/0.76      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.58/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.76  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 0.58/0.76      inference('demod', [status(thm)], ['9', '10'])).
% 0.58/0.76  thf('12', plain,
% 0.58/0.76      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2))),
% 0.58/0.76      inference('demod', [status(thm)], ['6', '11'])).
% 0.58/0.76  thf(t7_ordinal1, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.76  thf('13', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.58/0.76      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.76  thf('14', plain,
% 0.58/0.76      (~ (r1_tarski @ (k1_relat_1 @ sk_D_2) @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.76  thf('15', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(t22_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.58/0.76       ( ( ![D:$i]:
% 0.58/0.76           ( ~( ( r2_hidden @ D @ B ) & 
% 0.58/0.76                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.58/0.76         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.58/0.76  thf('16', plain,
% 0.58/0.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.58/0.76         ((r2_hidden @ (sk_D_1 @ X26 @ X24) @ X24)
% 0.58/0.76          | ((k1_relset_1 @ X24 @ X25 @ X26) = (X24))
% 0.58/0.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.58/0.76      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.58/0.76  thf('17', plain,
% 0.58/0.76      ((((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (sk_A))
% 0.58/0.76        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_A) @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.76  thf('18', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.76  thf('19', plain,
% 0.58/0.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.76         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.58/0.76          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.58/0.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.76  thf('20', plain,
% 0.58/0.76      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.58/0.76      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.76  thf('21', plain,
% 0.58/0.76      ((((k1_relat_1 @ sk_D_2) = (sk_A))
% 0.58/0.76        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_A) @ sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['17', '20'])).
% 0.58/0.76  thf('22', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.58/0.76      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.76  thf('23', plain,
% 0.58/0.76      ((((k1_relat_1 @ sk_D_2) = (sk_A))
% 0.58/0.76        | ~ (r1_tarski @ sk_A @ (sk_D_1 @ sk_D_2 @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.58/0.76  thf('24', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(d1_funct_2, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_1, axiom,
% 0.58/0.76    (![B:$i,A:$i]:
% 0.58/0.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.76       ( zip_tseitin_0 @ B @ A ) ))).
% 0.58/0.76  thf('25', plain,
% 0.58/0.76      (![X29 : $i, X30 : $i]:
% 0.58/0.76         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.76  thf('26', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.58/0.76  thf(zf_stmt_3, axiom,
% 0.58/0.76    (![C:$i,B:$i,A:$i]:
% 0.58/0.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.58/0.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.58/0.76  thf(zf_stmt_5, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.58/0.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.76  thf('27', plain,
% 0.58/0.76      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.76         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.58/0.76          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.58/0.76          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.76  thf('28', plain,
% 0.58/0.76      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.58/0.76        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.76  thf('29', plain,
% 0.58/0.76      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['25', '28'])).
% 0.58/0.76  thf('30', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('31', plain,
% 0.58/0.76      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.58/0.76         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.58/0.76          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.58/0.76          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.76  thf('32', plain,
% 0.58/0.76      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.58/0.76        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.58/0.76  thf('33', plain,
% 0.58/0.76      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.58/0.76      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.76  thf('34', plain,
% 0.58/0.76      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.58/0.76        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.58/0.76      inference('demod', [status(thm)], ['32', '33'])).
% 0.58/0.76  thf('35', plain,
% 0.58/0.76      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['29', '34'])).
% 0.58/0.76  thf('36', plain,
% 0.58/0.76      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2))),
% 0.58/0.76      inference('demod', [status(thm)], ['6', '11'])).
% 0.58/0.76  thf('37', plain,
% 0.58/0.76      (((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_A)
% 0.58/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['35', '36'])).
% 0.58/0.76  thf('38', plain,
% 0.58/0.76      (![X37 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X37 @ sk_A)
% 0.58/0.76          | ~ (r2_hidden @ X37 @ sk_C)
% 0.58/0.76          | ((sk_E_1) != (k1_funct_1 @ sk_D_2 @ X37)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('39', plain,
% 0.58/0.76      ((((sk_B) = (k1_xboole_0))
% 0.58/0.76        | ((sk_E_1) != (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1)))
% 0.58/0.76        | ~ (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C))),
% 0.58/0.76      inference('sup-', [status(thm)], ['37', '38'])).
% 0.58/0.76  thf('40', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.76  thf('41', plain,
% 0.58/0.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.58/0.76          | (r2_hidden @ (k4_tarski @ (sk_D @ X11 @ X9 @ X10) @ X10) @ X11)
% 0.58/0.76          | ~ (v1_relat_1 @ X11))),
% 0.58/0.76      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.58/0.76  thf('42', plain,
% 0.58/0.76      ((~ (v1_relat_1 @ sk_D_2)
% 0.58/0.76        | (r2_hidden @ 
% 0.58/0.76           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1) @ sk_D_2))),
% 0.58/0.76      inference('sup-', [status(thm)], ['40', '41'])).
% 0.58/0.76  thf('43', plain, ((v1_relat_1 @ sk_D_2)),
% 0.58/0.76      inference('demod', [status(thm)], ['9', '10'])).
% 0.58/0.76  thf('44', plain,
% 0.58/0.76      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1) @ 
% 0.58/0.76        sk_D_2)),
% 0.58/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.58/0.76  thf(t8_funct_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.58/0.76       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.58/0.76         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.58/0.76           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.58/0.76  thf('45', plain,
% 0.58/0.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.76         (~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ X13)
% 0.58/0.76          | ((X14) = (k1_funct_1 @ X13 @ X12))
% 0.58/0.76          | ~ (v1_funct_1 @ X13)
% 0.58/0.76          | ~ (v1_relat_1 @ X13))),
% 0.58/0.76      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.58/0.76  thf('46', plain,
% 0.58/0.76      ((~ (v1_relat_1 @ sk_D_2)
% 0.58/0.76        | ~ (v1_funct_1 @ sk_D_2)
% 0.58/0.76        | ((sk_E_1) = (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['44', '45'])).
% 0.58/0.76  thf('47', plain, ((v1_relat_1 @ sk_D_2)),
% 0.58/0.76      inference('demod', [status(thm)], ['9', '10'])).
% 0.58/0.76  thf('48', plain, ((v1_funct_1 @ sk_D_2)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('49', plain,
% 0.58/0.76      (((sk_E_1) = (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1)))),
% 0.58/0.76      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.58/0.76  thf('50', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.76  thf('51', plain,
% 0.58/0.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.58/0.76          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ X9)
% 0.58/0.76          | ~ (v1_relat_1 @ X11))),
% 0.58/0.76      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.58/0.76  thf('52', plain,
% 0.58/0.76      ((~ (v1_relat_1 @ sk_D_2)
% 0.58/0.76        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C))),
% 0.58/0.76      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.76  thf('53', plain, ((v1_relat_1 @ sk_D_2)),
% 0.58/0.76      inference('demod', [status(thm)], ['9', '10'])).
% 0.58/0.76  thf('54', plain, ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C)),
% 0.58/0.76      inference('demod', [status(thm)], ['52', '53'])).
% 0.58/0.76  thf('55', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E_1) != (sk_E_1)))),
% 0.58/0.76      inference('demod', [status(thm)], ['39', '49', '54'])).
% 0.58/0.76  thf('56', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.76      inference('simplify', [status(thm)], ['55'])).
% 0.58/0.76  thf('57', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D_2 @ 
% 0.58/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.58/0.76      inference('demod', [status(thm)], ['24', '56'])).
% 0.58/0.76  thf('58', plain,
% 0.58/0.76      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.76         (((X34) != (k1_xboole_0))
% 0.58/0.76          | ((X35) = (k1_xboole_0))
% 0.58/0.76          | ((X36) = (k1_xboole_0))
% 0.58/0.76          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.58/0.76          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.76  thf('59', plain,
% 0.58/0.76      (![X35 : $i, X36 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X36 @ 
% 0.58/0.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ k1_xboole_0)))
% 0.58/0.76          | ~ (v1_funct_2 @ X36 @ X35 @ k1_xboole_0)
% 0.58/0.76          | ((X36) = (k1_xboole_0))
% 0.58/0.76          | ((X35) = (k1_xboole_0)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['58'])).
% 0.58/0.76  thf('60', plain,
% 0.58/0.76      ((((sk_A) = (k1_xboole_0))
% 0.58/0.76        | ((sk_D_2) = (k1_xboole_0))
% 0.58/0.76        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['57', '59'])).
% 0.58/0.76  thf('61', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('62', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.76      inference('simplify', [status(thm)], ['55'])).
% 0.58/0.76  thf('63', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0)),
% 0.58/0.76      inference('demod', [status(thm)], ['61', '62'])).
% 0.58/0.76  thf('64', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 0.58/0.76      inference('demod', [status(thm)], ['60', '63'])).
% 0.58/0.76  thf('65', plain,
% 0.58/0.76      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1) @ 
% 0.58/0.76        sk_D_2)),
% 0.58/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.58/0.76  thf('66', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.58/0.76      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.76  thf('67', plain,
% 0.58/0.76      (~ (r1_tarski @ sk_D_2 @ 
% 0.58/0.76          (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.76  thf('68', plain,
% 0.58/0.76      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.58/0.76           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1))
% 0.58/0.76        | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['64', '67'])).
% 0.58/0.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.76  thf('69', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.76  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.76      inference('demod', [status(thm)], ['68', '69'])).
% 0.58/0.76  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.76      inference('demod', [status(thm)], ['68', '69'])).
% 0.58/0.76  thf('72', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.76      inference('demod', [status(thm)], ['68', '69'])).
% 0.58/0.76  thf('73', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.76  thf('74', plain, (((k1_relat_1 @ sk_D_2) = (k1_xboole_0))),
% 0.58/0.76      inference('demod', [status(thm)], ['23', '70', '71', '72', '73'])).
% 0.58/0.76  thf('75', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.76  thf('76', plain, ($false),
% 0.58/0.76      inference('demod', [status(thm)], ['14', '74', '75'])).
% 0.58/0.76  
% 0.58/0.76  % SZS output end Refutation
% 0.58/0.76  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
