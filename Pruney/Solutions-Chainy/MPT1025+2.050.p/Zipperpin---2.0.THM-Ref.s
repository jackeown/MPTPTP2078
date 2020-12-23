%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d7OWSY1bDG

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:50 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  139 (1533 expanded)
%              Number of leaves         :   39 ( 467 expanded)
%              Depth                    :   21
%              Number of atoms          :  913 (20712 expanded)
%              Number of equality atoms :   65 ( 857 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X11 @ X12 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('24',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( m1_subset_1 @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('39',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X32: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X32 ) )
      | ~ ( r2_hidden @ X32 @ sk_C )
      | ~ ( m1_subset_1 @ X32 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X11 @ X12 ) @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('47',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X15 )
      | ( X16
        = ( k1_funct_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('51',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['42','52'])).

thf('54',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['21','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf('58',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 != k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf('64',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('73',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['55','71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('75',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('76',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('80',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('81',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['79','81'])).

thf('83',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['88','91'])).

thf('93',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('94',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['78','94'])).

thf('96',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['73','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['14','96','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d7OWSY1bDG
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 230 iterations in 0.266s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.73  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.73  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.52/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.73  thf(sk_E_type, type, sk_E: $i).
% 0.52/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.52/0.73  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.52/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.73  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.52/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.52/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.52/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.73  thf(t116_funct_2, conjecture,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.73       ( ![E:$i]:
% 0.52/0.73         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.52/0.73              ( ![F:$i]:
% 0.52/0.73                ( ( m1_subset_1 @ F @ A ) =>
% 0.52/0.73                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.52/0.73                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.73            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.73          ( ![E:$i]:
% 0.52/0.73            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.52/0.73                 ( ![F:$i]:
% 0.52/0.73                   ( ( m1_subset_1 @ F @ A ) =>
% 0.52/0.73                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.52/0.73                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.52/0.73  thf('0', plain,
% 0.52/0.73      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(redefinition_k7_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.52/0.73  thf('2', plain,
% 0.52/0.73      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.52/0.73          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.52/0.73           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.73  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['0', '3'])).
% 0.52/0.73  thf(t143_relat_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( v1_relat_1 @ C ) =>
% 0.52/0.73       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.52/0.73         ( ?[D:$i]:
% 0.52/0.73           ( ( r2_hidden @ D @ B ) & 
% 0.52/0.73             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.52/0.73             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.52/0.73          | (r2_hidden @ (sk_D @ X13 @ X11 @ X12) @ (k1_relat_1 @ X13))
% 0.52/0.73          | ~ (v1_relat_1 @ X13))),
% 0.52/0.73      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.52/0.73  thf('6', plain,
% 0.52/0.73      ((~ (v1_relat_1 @ sk_D_1)
% 0.52/0.73        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.73  thf('7', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(cc2_relat_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( v1_relat_1 @ A ) =>
% 0.52/0.73       ( ![B:$i]:
% 0.52/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      (![X6 : $i, X7 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.52/0.73          | (v1_relat_1 @ X6)
% 0.52/0.73          | ~ (v1_relat_1 @ X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.73  thf('9', plain,
% 0.52/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.52/0.73  thf(fc6_relat_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.52/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.73  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.52/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf('12', plain,
% 0.52/0.73      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.52/0.73      inference('demod', [status(thm)], ['6', '11'])).
% 0.52/0.73  thf(d1_xboole_0, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.52/0.73  thf('13', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.73  thf('14', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.73  thf('15', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(d1_funct_2, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.52/0.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.52/0.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.52/0.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_1, axiom,
% 0.52/0.73    (![C:$i,B:$i,A:$i]:
% 0.52/0.73     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.52/0.73       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.52/0.73  thf('16', plain,
% 0.52/0.73      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.52/0.73         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.52/0.73          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 0.52/0.73          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.52/0.73        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.52/0.73  thf('19', plain,
% 0.52/0.73      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.52/0.73         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.52/0.73          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.73  thf('21', plain,
% 0.52/0.73      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.52/0.73        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.52/0.73      inference('demod', [status(thm)], ['17', '20'])).
% 0.52/0.73  thf(zf_stmt_2, axiom,
% 0.52/0.73    (![B:$i,A:$i]:
% 0.52/0.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.73       ( zip_tseitin_0 @ B @ A ) ))).
% 0.52/0.73  thf('22', plain,
% 0.52/0.73      (![X24 : $i, X25 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.73  thf('23', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.52/0.73  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.52/0.73  thf(zf_stmt_5, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.52/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.52/0.73         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.52/0.73          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.52/0.73          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.73  thf('25', plain,
% 0.52/0.73      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.52/0.73        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.73  thf('26', plain,
% 0.52/0.73      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['22', '25'])).
% 0.52/0.73  thf('27', plain,
% 0.52/0.73      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.52/0.73        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.52/0.73      inference('demod', [status(thm)], ['17', '20'])).
% 0.52/0.73  thf('28', plain,
% 0.52/0.73      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.52/0.73  thf('29', plain,
% 0.52/0.73      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.52/0.73      inference('demod', [status(thm)], ['6', '11'])).
% 0.52/0.73  thf('30', plain,
% 0.52/0.73      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.52/0.73        | ((sk_B_1) = (k1_xboole_0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['28', '29'])).
% 0.52/0.73  thf(d2_subset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( v1_xboole_0 @ A ) =>
% 0.52/0.73         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.52/0.73       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.52/0.73         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.52/0.73  thf('31', plain,
% 0.52/0.73      (![X3 : $i, X4 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X3 @ X4)
% 0.52/0.73          | (m1_subset_1 @ X3 @ X4)
% 0.52/0.73          | (v1_xboole_0 @ X4))),
% 0.52/0.73      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.52/0.73  thf('32', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.52/0.73      inference('clc', [status(thm)], ['31', '32'])).
% 0.52/0.73  thf('34', plain,
% 0.52/0.73      ((((sk_B_1) = (k1_xboole_0))
% 0.52/0.73        | (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['30', '33'])).
% 0.52/0.73  thf('35', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['0', '3'])).
% 0.52/0.73  thf('36', plain,
% 0.52/0.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.52/0.73          | (r2_hidden @ (sk_D @ X13 @ X11 @ X12) @ X11)
% 0.52/0.73          | ~ (v1_relat_1 @ X13))),
% 0.52/0.73      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.52/0.73  thf('37', plain,
% 0.52/0.73      ((~ (v1_relat_1 @ sk_D_1)
% 0.52/0.73        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['35', '36'])).
% 0.52/0.73  thf('38', plain, ((v1_relat_1 @ sk_D_1)),
% 0.52/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf('39', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.52/0.73      inference('demod', [status(thm)], ['37', '38'])).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      (![X32 : $i]:
% 0.52/0.73         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X32))
% 0.52/0.73          | ~ (r2_hidden @ X32 @ sk_C)
% 0.52/0.73          | ~ (m1_subset_1 @ X32 @ sk_A))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('41', plain,
% 0.52/0.73      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.52/0.73        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.73  thf('42', plain,
% 0.52/0.73      ((((sk_B_1) = (k1_xboole_0))
% 0.52/0.73        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['34', '41'])).
% 0.52/0.73  thf('43', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['0', '3'])).
% 0.52/0.73  thf('44', plain,
% 0.52/0.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.52/0.73          | (r2_hidden @ (k4_tarski @ (sk_D @ X13 @ X11 @ X12) @ X12) @ X13)
% 0.52/0.73          | ~ (v1_relat_1 @ X13))),
% 0.52/0.73      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.52/0.73  thf('45', plain,
% 0.52/0.73      ((~ (v1_relat_1 @ sk_D_1)
% 0.52/0.73        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.52/0.73           sk_D_1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['43', '44'])).
% 0.52/0.73  thf('46', plain, ((v1_relat_1 @ sk_D_1)),
% 0.52/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf('47', plain,
% 0.52/0.73      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.52/0.73      inference('demod', [status(thm)], ['45', '46'])).
% 0.52/0.73  thf(t8_funct_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.52/0.73       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.52/0.73         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.52/0.73           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.52/0.73  thf('48', plain,
% 0.52/0.73      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.52/0.73         (~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X15)
% 0.52/0.73          | ((X16) = (k1_funct_1 @ X15 @ X14))
% 0.52/0.73          | ~ (v1_funct_1 @ X15)
% 0.52/0.73          | ~ (v1_relat_1 @ X15))),
% 0.52/0.73      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.52/0.73  thf('49', plain,
% 0.52/0.73      ((~ (v1_relat_1 @ sk_D_1)
% 0.52/0.73        | ~ (v1_funct_1 @ sk_D_1)
% 0.52/0.73        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.52/0.73  thf('50', plain, ((v1_relat_1 @ sk_D_1)),
% 0.52/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf('51', plain, ((v1_funct_1 @ sk_D_1)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('52', plain,
% 0.52/0.73      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.52/0.73      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.52/0.73  thf('53', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 0.52/0.73      inference('demod', [status(thm)], ['42', '52'])).
% 0.52/0.73  thf('54', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['53'])).
% 0.52/0.73  thf('55', plain,
% 0.52/0.73      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A)
% 0.52/0.73        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.52/0.73      inference('demod', [status(thm)], ['21', '54'])).
% 0.52/0.73  thf('56', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('57', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['53'])).
% 0.52/0.73  thf('58', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.73  thf('59', plain,
% 0.52/0.73      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.52/0.73         (((X29) != (k1_xboole_0))
% 0.52/0.73          | ((X30) = (k1_xboole_0))
% 0.52/0.73          | ((X31) = (k1_xboole_0))
% 0.52/0.73          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 0.52/0.73          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.73  thf('60', plain,
% 0.52/0.73      (![X30 : $i, X31 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X31 @ 
% 0.52/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ k1_xboole_0)))
% 0.52/0.73          | ~ (v1_funct_2 @ X31 @ X30 @ k1_xboole_0)
% 0.52/0.73          | ((X31) = (k1_xboole_0))
% 0.52/0.73          | ((X30) = (k1_xboole_0)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['59'])).
% 0.52/0.73  thf('61', plain,
% 0.52/0.73      ((((sk_A) = (k1_xboole_0))
% 0.52/0.73        | ((sk_D_1) = (k1_xboole_0))
% 0.52/0.73        | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['58', '60'])).
% 0.52/0.73  thf('62', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('63', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['53'])).
% 0.52/0.73  thf('64', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0)),
% 0.52/0.73      inference('demod', [status(thm)], ['62', '63'])).
% 0.52/0.73  thf('65', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_1) = (k1_xboole_0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['61', '64'])).
% 0.52/0.73  thf('66', plain,
% 0.52/0.73      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.52/0.73      inference('demod', [status(thm)], ['45', '46'])).
% 0.52/0.73  thf('67', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.73  thf('68', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.52/0.73      inference('sup-', [status(thm)], ['66', '67'])).
% 0.52/0.73  thf('69', plain,
% 0.52/0.73      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['65', '68'])).
% 0.52/0.73  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.52/0.73  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.73  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['69', '70'])).
% 0.52/0.73  thf('72', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['69', '70'])).
% 0.52/0.73  thf('73', plain,
% 0.52/0.73      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.52/0.73        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_1)))),
% 0.52/0.73      inference('demod', [status(thm)], ['55', '71', '72'])).
% 0.52/0.73  thf('74', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.73  thf('75', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['69', '70'])).
% 0.52/0.73  thf('76', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['74', '75'])).
% 0.52/0.73  thf('77', plain,
% 0.52/0.73      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.52/0.73         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.52/0.73          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.52/0.73          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.73  thf('78', plain,
% 0.52/0.73      (((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.52/0.73        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['76', '77'])).
% 0.52/0.73  thf('79', plain,
% 0.52/0.73      (![X24 : $i, X25 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.73  thf('80', plain,
% 0.52/0.73      (![X24 : $i, X25 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.73  thf('81', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 0.52/0.73      inference('simplify', [status(thm)], ['80'])).
% 0.52/0.73  thf('82', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.52/0.73      inference('sup+', [status(thm)], ['79', '81'])).
% 0.52/0.73  thf('83', plain,
% 0.52/0.73      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.52/0.73        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.73  thf('84', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ sk_A @ X0)
% 0.52/0.73          | (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['82', '83'])).
% 0.52/0.73  thf('85', plain,
% 0.52/0.73      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.52/0.73        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.52/0.73      inference('demod', [status(thm)], ['17', '20'])).
% 0.52/0.73  thf('86', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['84', '85'])).
% 0.52/0.73  thf('87', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.73  thf('88', plain,
% 0.52/0.73      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | (zip_tseitin_0 @ sk_A @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['86', '87'])).
% 0.52/0.73  thf('89', plain,
% 0.52/0.73      (![X24 : $i, X25 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.73  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.73  thf('91', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.52/0.73      inference('sup+', [status(thm)], ['89', '90'])).
% 0.52/0.73  thf('92', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 0.52/0.73      inference('clc', [status(thm)], ['88', '91'])).
% 0.52/0.73  thf('93', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['69', '70'])).
% 0.52/0.73  thf('94', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 0.52/0.73      inference('demod', [status(thm)], ['92', '93'])).
% 0.52/0.73  thf('95', plain, ((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.52/0.73      inference('demod', [status(thm)], ['78', '94'])).
% 0.52/0.73  thf('96', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_1))),
% 0.52/0.73      inference('demod', [status(thm)], ['73', '95'])).
% 0.52/0.73  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.73  thf('98', plain, ($false),
% 0.52/0.73      inference('demod', [status(thm)], ['14', '96', '97'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
