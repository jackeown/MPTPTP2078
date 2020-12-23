%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m0XyRGNHRt

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:41 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  153 (1504 expanded)
%              Number of leaves         :   39 ( 458 expanded)
%              Depth                    :   21
%              Number of atoms          : 1026 (20476 expanded)
%              Number of equality atoms :   66 ( 857 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k7_relset_1 @ X18 @ X19 @ X17 @ X20 )
        = ( k9_relat_1 @ X17 @ X20 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X8 @ X9 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
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

thf('31',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ sk_A )
      | ~ ( r2_hidden @ X29 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X8 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('37',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X10 @ X8 @ X9 ) @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('43',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['41','42'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ X12 )
      | ( X13
        = ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('47',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['38','48'])).

thf('50',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['21','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('60',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('63',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X10 @ X8 @ X9 ) @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','74'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76'])).

thf('79',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['51','77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76'])).

thf('82',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('84',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('86',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('87',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['85','87'])).

thf('89',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('94',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X8 @ X9 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ X1 ) ) ),
    inference(clc,[status(thm)],['100','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('106',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76'])).

thf('108',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['84','108'])).

thf('110',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['79','109'])).

thf('111',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('112',plain,(
    $false ),
    inference(demod,[status(thm)],['14','110','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m0XyRGNHRt
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:06:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 191 iterations in 0.250s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.49/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.49/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(sk_E_type, type, sk_E: $i).
% 0.49/0.72  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.49/0.72  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.49/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.49/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.49/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.49/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.49/0.72  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.49/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.72  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.72  thf(t115_funct_2, conjecture,
% 0.49/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.72     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.49/0.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.72       ( ![E:$i]:
% 0.49/0.72         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.49/0.72              ( ![F:$i]:
% 0.49/0.72                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.49/0.72                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.72        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.49/0.72            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.72          ( ![E:$i]:
% 0.49/0.72            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.49/0.72                 ( ![F:$i]:
% 0.49/0.72                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.49/0.72                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.49/0.72  thf('0', plain,
% 0.49/0.72      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(redefinition_k7_relset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.49/0.72  thf('2', plain,
% 0.49/0.72      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.49/0.72          | ((k7_relset_1 @ X18 @ X19 @ X17 @ X20) = (k9_relat_1 @ X17 @ X20)))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.49/0.72  thf('3', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.49/0.72           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.72  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['0', '3'])).
% 0.49/0.72  thf(t143_relat_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( v1_relat_1 @ C ) =>
% 0.49/0.72       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.49/0.72         ( ?[D:$i]:
% 0.49/0.72           ( ( r2_hidden @ D @ B ) & 
% 0.49/0.72             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.49/0.72             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.49/0.72  thf('5', plain,
% 0.49/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.49/0.72          | (r2_hidden @ (sk_D @ X10 @ X8 @ X9) @ (k1_relat_1 @ X10))
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.49/0.72  thf('6', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_D_1)
% 0.49/0.72        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.72  thf('7', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(cc2_relat_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v1_relat_1 @ A ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.49/0.72  thf('8', plain,
% 0.49/0.72      (![X3 : $i, X4 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.49/0.72          | (v1_relat_1 @ X3)
% 0.49/0.72          | ~ (v1_relat_1 @ X4))),
% 0.49/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.49/0.72  thf('9', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.72  thf(fc6_relat_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.49/0.72  thf('10', plain,
% 0.49/0.72      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.49/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.49/0.72  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('12', plain,
% 0.49/0.72      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '11'])).
% 0.49/0.72  thf(d1_xboole_0, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.49/0.72  thf('13', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.72  thf('14', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.72  thf('15', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(d1_funct_2, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.49/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.49/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.49/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_1, axiom,
% 0.49/0.72    (![C:$i,B:$i,A:$i]:
% 0.49/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.49/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.49/0.72  thf('16', plain,
% 0.49/0.72      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.49/0.72         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.49/0.72          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.49/0.72          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.49/0.72  thf('17', plain,
% 0.49/0.72      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['15', '16'])).
% 0.49/0.72  thf('18', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.49/0.72  thf('19', plain,
% 0.49/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.72         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.49/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.72  thf('20', plain,
% 0.49/0.72      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['18', '19'])).
% 0.49/0.72  thf('21', plain,
% 0.49/0.72      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.72        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.72      inference('demod', [status(thm)], ['17', '20'])).
% 0.49/0.72  thf(zf_stmt_2, axiom,
% 0.49/0.72    (![B:$i,A:$i]:
% 0.49/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.49/0.72  thf('22', plain,
% 0.49/0.72      (![X21 : $i, X22 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.72  thf('23', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.49/0.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.49/0.72  thf(zf_stmt_5, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.49/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.49/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.49/0.72  thf('24', plain,
% 0.49/0.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.72         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.49/0.72          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.49/0.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.72  thf('25', plain,
% 0.49/0.72      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.72        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.72  thf('26', plain,
% 0.49/0.72      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['22', '25'])).
% 0.49/0.72  thf('27', plain,
% 0.49/0.72      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.72        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.72      inference('demod', [status(thm)], ['17', '20'])).
% 0.49/0.72  thf('28', plain,
% 0.49/0.72      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.49/0.72  thf('29', plain,
% 0.49/0.72      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '11'])).
% 0.49/0.72  thf('30', plain,
% 0.49/0.72      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.49/0.72        | ((sk_B_1) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['28', '29'])).
% 0.49/0.72  thf('31', plain,
% 0.49/0.72      (![X29 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X29 @ sk_A)
% 0.49/0.72          | ~ (r2_hidden @ X29 @ sk_C)
% 0.49/0.72          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X29)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('32', plain,
% 0.49/0.72      ((((sk_B_1) = (k1_xboole_0))
% 0.49/0.72        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))
% 0.49/0.72        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['30', '31'])).
% 0.49/0.72  thf('33', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['0', '3'])).
% 0.49/0.72  thf('34', plain,
% 0.49/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.49/0.72          | (r2_hidden @ (sk_D @ X10 @ X8 @ X9) @ X8)
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.49/0.72  thf('35', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_D_1)
% 0.49/0.72        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.72  thf('36', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('37', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.49/0.72      inference('demod', [status(thm)], ['35', '36'])).
% 0.49/0.72  thf('38', plain,
% 0.49/0.72      ((((sk_B_1) = (k1_xboole_0))
% 0.49/0.72        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.49/0.72      inference('demod', [status(thm)], ['32', '37'])).
% 0.49/0.72  thf('39', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['0', '3'])).
% 0.49/0.72  thf('40', plain,
% 0.49/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.49/0.72          | (r2_hidden @ (k4_tarski @ (sk_D @ X10 @ X8 @ X9) @ X9) @ X10)
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.49/0.72  thf('41', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_D_1)
% 0.49/0.72        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.49/0.72           sk_D_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['39', '40'])).
% 0.49/0.72  thf('42', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('43', plain,
% 0.49/0.72      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.49/0.72      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.72  thf(t8_funct_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.72       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.49/0.72         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.49/0.72           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.49/0.72  thf('44', plain,
% 0.49/0.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.72         (~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ X12)
% 0.49/0.72          | ((X13) = (k1_funct_1 @ X12 @ X11))
% 0.49/0.72          | ~ (v1_funct_1 @ X12)
% 0.49/0.72          | ~ (v1_relat_1 @ X12))),
% 0.49/0.72      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.49/0.72  thf('45', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_D_1)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_D_1)
% 0.49/0.72        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['43', '44'])).
% 0.49/0.72  thf('46', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('47', plain, ((v1_funct_1 @ sk_D_1)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('48', plain,
% 0.49/0.72      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.49/0.72      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.49/0.72  thf('49', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 0.49/0.72      inference('demod', [status(thm)], ['38', '48'])).
% 0.49/0.72  thf('50', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['49'])).
% 0.49/0.72  thf('51', plain,
% 0.49/0.72      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A)
% 0.49/0.72        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.72      inference('demod', [status(thm)], ['21', '50'])).
% 0.49/0.72  thf('52', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('53', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['49'])).
% 0.49/0.72  thf('54', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.49/0.72      inference('demod', [status(thm)], ['52', '53'])).
% 0.49/0.72  thf('55', plain,
% 0.49/0.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.72         (((X26) != (k1_xboole_0))
% 0.49/0.72          | ((X27) = (k1_xboole_0))
% 0.49/0.72          | ((X28) = (k1_xboole_0))
% 0.49/0.72          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.49/0.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.72  thf('56', plain,
% 0.49/0.72      (![X27 : $i, X28 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X28 @ 
% 0.49/0.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ k1_xboole_0)))
% 0.49/0.72          | ~ (v1_funct_2 @ X28 @ X27 @ k1_xboole_0)
% 0.49/0.72          | ((X28) = (k1_xboole_0))
% 0.49/0.72          | ((X27) = (k1_xboole_0)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['55'])).
% 0.49/0.72  thf('57', plain,
% 0.49/0.72      ((((sk_A) = (k1_xboole_0))
% 0.49/0.72        | ((sk_D_1) = (k1_xboole_0))
% 0.49/0.72        | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['54', '56'])).
% 0.49/0.72  thf('58', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('59', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['49'])).
% 0.49/0.72  thf('60', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0)),
% 0.49/0.72      inference('demod', [status(thm)], ['58', '59'])).
% 0.49/0.72  thf('61', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_1) = (k1_xboole_0)))),
% 0.49/0.72      inference('demod', [status(thm)], ['57', '60'])).
% 0.49/0.72  thf('62', plain,
% 0.49/0.72      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.49/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.72  thf('63', plain,
% 0.49/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.49/0.72          | (r2_hidden @ (k4_tarski @ (sk_D @ X10 @ X8 @ X9) @ X9) @ X10)
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.49/0.72  thf('64', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.49/0.72          | ~ (v1_relat_1 @ X1)
% 0.49/0.72          | (r2_hidden @ 
% 0.49/0.72             (k4_tarski @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.49/0.72              (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.49/0.72             X1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.72  thf('65', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.72  thf('66', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.49/0.72          | ~ (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['64', '65'])).
% 0.49/0.72  thf('67', plain,
% 0.49/0.72      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('68', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.72  thf('69', plain,
% 0.49/0.72      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['67', '68'])).
% 0.49/0.72  thf('70', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.49/0.72           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.72  thf('71', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['69', '70'])).
% 0.49/0.72  thf('72', plain, ((~ (v1_xboole_0 @ sk_D_1) | ~ (v1_relat_1 @ sk_D_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['66', '71'])).
% 0.49/0.72  thf('73', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('74', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.49/0.72      inference('demod', [status(thm)], ['72', '73'])).
% 0.49/0.72  thf('75', plain,
% 0.49/0.72      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['61', '74'])).
% 0.49/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.49/0.72  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('77', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['75', '76'])).
% 0.49/0.72  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['75', '76'])).
% 0.49/0.72  thf('79', plain,
% 0.49/0.72      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.49/0.72        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.72      inference('demod', [status(thm)], ['51', '77', '78'])).
% 0.49/0.72  thf('80', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.49/0.72      inference('demod', [status(thm)], ['52', '53'])).
% 0.49/0.72  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['75', '76'])).
% 0.49/0.72  thf('82', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.49/0.72      inference('demod', [status(thm)], ['80', '81'])).
% 0.49/0.72  thf('83', plain,
% 0.49/0.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.72         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.49/0.72          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.49/0.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.72  thf('84', plain,
% 0.49/0.72      (((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.49/0.72        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['82', '83'])).
% 0.49/0.72  thf('85', plain,
% 0.49/0.72      (![X21 : $i, X22 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.72  thf('86', plain,
% 0.49/0.72      (![X21 : $i, X22 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X21 @ X22) | ((X22) != (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.72  thf('87', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 0.49/0.72      inference('simplify', [status(thm)], ['86'])).
% 0.49/0.72  thf('88', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.49/0.72      inference('sup+', [status(thm)], ['85', '87'])).
% 0.49/0.72  thf('89', plain,
% 0.49/0.72      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.72        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.72  thf('90', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ sk_A @ X0)
% 0.49/0.72          | (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['88', '89'])).
% 0.49/0.72  thf('91', plain,
% 0.49/0.72      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.72        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.72      inference('demod', [status(thm)], ['17', '20'])).
% 0.49/0.72  thf('92', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['90', '91'])).
% 0.49/0.72  thf('93', plain,
% 0.49/0.72      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.49/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.72  thf('94', plain,
% 0.49/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.49/0.72          | (r2_hidden @ (sk_D @ X10 @ X8 @ X9) @ (k1_relat_1 @ X10))
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.49/0.72  thf('95', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.49/0.72          | ~ (v1_relat_1 @ X1)
% 0.49/0.72          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.49/0.72             (k1_relat_1 @ X1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['93', '94'])).
% 0.49/0.72  thf('96', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.72  thf('97', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.49/0.72          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['95', '96'])).
% 0.49/0.72  thf('98', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ sk_A)
% 0.49/0.72          | (zip_tseitin_0 @ sk_A @ X1)
% 0.49/0.72          | (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.49/0.72          | ~ (v1_relat_1 @ sk_D_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['92', '97'])).
% 0.49/0.72  thf('99', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('100', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ sk_A)
% 0.49/0.72          | (zip_tseitin_0 @ sk_A @ X1)
% 0.49/0.72          | (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.49/0.72      inference('demod', [status(thm)], ['98', '99'])).
% 0.49/0.72  thf('101', plain,
% 0.49/0.72      (![X21 : $i, X22 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.72  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('103', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.49/0.72      inference('sup+', [status(thm)], ['101', '102'])).
% 0.49/0.72  thf('104', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.49/0.72          | (zip_tseitin_0 @ sk_A @ X1))),
% 0.49/0.72      inference('clc', [status(thm)], ['100', '103'])).
% 0.49/0.72  thf('105', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['69', '70'])).
% 0.49/0.72  thf('106', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 0.49/0.72      inference('sup-', [status(thm)], ['104', '105'])).
% 0.49/0.72  thf('107', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['75', '76'])).
% 0.49/0.72  thf('108', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 0.49/0.72      inference('demod', [status(thm)], ['106', '107'])).
% 0.49/0.72  thf('109', plain, ((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('demod', [status(thm)], ['84', '108'])).
% 0.49/0.72  thf('110', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_1))),
% 0.49/0.72      inference('demod', [status(thm)], ['79', '109'])).
% 0.49/0.72  thf('111', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('112', plain, ($false),
% 0.49/0.72      inference('demod', [status(thm)], ['14', '110', '111'])).
% 0.49/0.72  
% 0.49/0.72  % SZS output end Refutation
% 0.49/0.72  
% 0.49/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
