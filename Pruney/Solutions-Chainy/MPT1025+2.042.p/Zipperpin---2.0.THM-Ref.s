%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.63mLwd3DpP

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:49 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  167 (1589 expanded)
%              Number of leaves         :   45 ( 487 expanded)
%              Depth                    :   21
%              Number of atoms          : 1121 (21194 expanded)
%              Number of equality atoms :   70 ( 872 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
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
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ),
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
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1 ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('37',plain,(
    r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X47: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_3 @ X47 ) )
      | ~ ( r2_hidden @ X47 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X47 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X11 @ X12 ) @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('45',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ),
    inference(demod,[status(thm)],['43','44'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( X26
        = ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('49',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['40','50'])).

thf('52',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['21','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('56',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 != k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_3 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('62',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_3 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ),
    inference(demod,[status(thm)],['43','44'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('68',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('69',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('70',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','72'])).

thf('75',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['53','73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('77',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','72'])).

thf('78',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('82',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('83',plain,(
    ! [X39: $i] :
      ( zip_tseitin_0 @ X39 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['81','83'])).

thf('85',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( X17
       != ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ ( sk_D_2 @ X18 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('91',plain,(
    ! [X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ ( sk_D_2 @ X18 @ X15 ) @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_B @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','71'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('104',plain,(
    ! [X15: $i,X17: $i,X19: $i,X20: $i] :
      ( ( X17
       != ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ X19 @ X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X15 ) )
      | ( X19
       != ( k1_funct_1 @ X15 @ X20 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('105',plain,(
    ! [X15: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ X20 ) @ ( k2_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('114',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','72'])).

thf('116',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['80','116'])).

thf('118',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['75','117'])).

thf('119',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','71'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['14','118','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.63mLwd3DpP
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:38:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.75/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.93  % Solved by: fo/fo7.sh
% 0.75/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.93  % done 380 iterations in 0.487s
% 0.75/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.93  % SZS output start Refutation
% 0.75/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.93  thf(sk_B_type, type, sk_B: $i > $i).
% 0.75/0.93  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.75/0.93  thf(sk_E_type, type, sk_E: $i).
% 0.75/0.93  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.75/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.93  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.75/0.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.75/0.93  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.75/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.93  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.75/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.93  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.93  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.75/0.93  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.75/0.93  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.75/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.93  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.75/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.93  thf(t116_funct_2, conjecture,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.75/0.93         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.93       ( ![E:$i]:
% 0.75/0.93         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.75/0.93              ( ![F:$i]:
% 0.75/0.93                ( ( m1_subset_1 @ F @ A ) =>
% 0.75/0.93                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.75/0.93                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.93    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.75/0.93            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.93          ( ![E:$i]:
% 0.75/0.93            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.75/0.93                 ( ![F:$i]:
% 0.75/0.93                   ( ( m1_subset_1 @ F @ A ) =>
% 0.75/0.93                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.75/0.93                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.75/0.93    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.75/0.93  thf('0', plain,
% 0.75/0.93      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ sk_C_1))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('1', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(redefinition_k7_relset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.75/0.93  thf('2', plain,
% 0.75/0.93      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.75/0.93          | ((k7_relset_1 @ X36 @ X37 @ X35 @ X38) = (k9_relat_1 @ X35 @ X38)))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.75/0.93  thf('3', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ X0)
% 0.75/0.93           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.93  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.75/0.93      inference('demod', [status(thm)], ['0', '3'])).
% 0.75/0.93  thf(t143_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ C ) =>
% 0.75/0.93       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.75/0.93         ( ?[D:$i]:
% 0.75/0.93           ( ( r2_hidden @ D @ B ) & 
% 0.75/0.93             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.75/0.93             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.75/0.93  thf('5', plain,
% 0.75/0.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.75/0.93          | (r2_hidden @ (sk_D @ X13 @ X11 @ X12) @ (k1_relat_1 @ X13))
% 0.75/0.93          | ~ (v1_relat_1 @ X13))),
% 0.75/0.93      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.75/0.93  thf('6', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ sk_D_3)
% 0.75/0.93        | (r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.93  thf('7', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(cc2_relat_1, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ A ) =>
% 0.75/0.93       ( ![B:$i]:
% 0.75/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.75/0.93  thf('8', plain,
% 0.75/0.93      (![X6 : $i, X7 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.75/0.93          | (v1_relat_1 @ X6)
% 0.75/0.93          | ~ (v1_relat_1 @ X7))),
% 0.75/0.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.75/0.93  thf('9', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_3))),
% 0.75/0.93      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.93  thf(fc6_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.75/0.93  thf('10', plain,
% 0.75/0.93      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.75/0.93  thf('11', plain, ((v1_relat_1 @ sk_D_3)),
% 0.75/0.93      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.93  thf('12', plain,
% 0.75/0.93      ((r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 0.75/0.93      inference('demod', [status(thm)], ['6', '11'])).
% 0.75/0.93  thf(d1_xboole_0, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.75/0.93  thf('13', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.93  thf('14', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_3))),
% 0.75/0.93      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.93  thf('15', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(d1_funct_2, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.93           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/0.93             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/0.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.93           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/0.93             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_1, axiom,
% 0.75/0.93    (![C:$i,B:$i,A:$i]:
% 0.75/0.93     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.75/0.93       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/0.93  thf('16', plain,
% 0.75/0.93      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.75/0.93         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.75/0.93          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.75/0.93          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.93  thf('17', plain,
% 0.75/0.93      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.75/0.93        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['15', '16'])).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(redefinition_k1_relset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/0.93  thf('19', plain,
% 0.75/0.93      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.75/0.93         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.75/0.93          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.93  thf('20', plain,
% 0.75/0.93      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.75/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.75/0.93  thf('21', plain,
% 0.75/0.93      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.75/0.93        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.75/0.93      inference('demod', [status(thm)], ['17', '20'])).
% 0.75/0.93  thf(zf_stmt_2, axiom,
% 0.75/0.93    (![B:$i,A:$i]:
% 0.75/0.93     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.93       ( zip_tseitin_0 @ B @ A ) ))).
% 0.75/0.93  thf('22', plain,
% 0.75/0.93      (![X39 : $i, X40 : $i]:
% 0.75/0.93         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.93  thf('23', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.75/0.93  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.75/0.93  thf(zf_stmt_5, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.75/0.93         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.93           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.93             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.75/0.93  thf('24', plain,
% 0.75/0.93      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.75/0.93         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.75/0.93          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.75/0.93          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.93  thf('25', plain,
% 0.75/0.93      (((zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.75/0.93        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.75/0.93      inference('sup-', [status(thm)], ['23', '24'])).
% 0.75/0.93  thf('26', plain,
% 0.75/0.93      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A))),
% 0.75/0.93      inference('sup-', [status(thm)], ['22', '25'])).
% 0.75/0.93  thf('27', plain,
% 0.75/0.93      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.75/0.93        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.75/0.93      inference('demod', [status(thm)], ['17', '20'])).
% 0.75/0.93  thf('28', plain,
% 0.75/0.93      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['26', '27'])).
% 0.75/0.93  thf('29', plain,
% 0.75/0.93      ((r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 0.75/0.93      inference('demod', [status(thm)], ['6', '11'])).
% 0.75/0.93  thf('30', plain,
% 0.75/0.93      (((r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A)
% 0.75/0.93        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['28', '29'])).
% 0.75/0.93  thf(t1_subset, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.75/0.93  thf('31', plain,
% 0.75/0.93      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.75/0.93      inference('cnf', [status(esa)], [t1_subset])).
% 0.75/0.93  thf('32', plain,
% 0.75/0.93      ((((sk_B_1) = (k1_xboole_0))
% 0.75/0.93        | (m1_subset_1 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A))),
% 0.75/0.93      inference('sup-', [status(thm)], ['30', '31'])).
% 0.75/0.93  thf('33', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.75/0.93      inference('demod', [status(thm)], ['0', '3'])).
% 0.75/0.93  thf('34', plain,
% 0.75/0.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.75/0.93          | (r2_hidden @ (sk_D @ X13 @ X11 @ X12) @ X11)
% 0.75/0.93          | ~ (v1_relat_1 @ X13))),
% 0.75/0.93      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.75/0.93  thf('35', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ sk_D_3)
% 0.75/0.93        | (r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/0.93  thf('36', plain, ((v1_relat_1 @ sk_D_3)),
% 0.75/0.93      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.93  thf('37', plain, ((r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 0.75/0.93      inference('demod', [status(thm)], ['35', '36'])).
% 0.75/0.93  thf('38', plain,
% 0.75/0.93      (![X47 : $i]:
% 0.75/0.93         (((sk_E) != (k1_funct_1 @ sk_D_3 @ X47))
% 0.75/0.93          | ~ (r2_hidden @ X47 @ sk_C_1)
% 0.75/0.93          | ~ (m1_subset_1 @ X47 @ sk_A))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('39', plain,
% 0.75/0.93      ((~ (m1_subset_1 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A)
% 0.75/0.93        | ((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['37', '38'])).
% 0.75/0.93  thf('40', plain,
% 0.75/0.93      ((((sk_B_1) = (k1_xboole_0))
% 0.75/0.93        | ((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['32', '39'])).
% 0.75/0.93  thf('41', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.75/0.93      inference('demod', [status(thm)], ['0', '3'])).
% 0.75/0.93  thf('42', plain,
% 0.75/0.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.75/0.93          | (r2_hidden @ (k4_tarski @ (sk_D @ X13 @ X11 @ X12) @ X12) @ X13)
% 0.75/0.93          | ~ (v1_relat_1 @ X13))),
% 0.75/0.94      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_D_3)
% 0.75/0.94        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.75/0.94           sk_D_3))),
% 0.75/0.94      inference('sup-', [status(thm)], ['41', '42'])).
% 0.75/0.94  thf('44', plain, ((v1_relat_1 @ sk_D_3)),
% 0.75/0.94      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.94  thf('45', plain,
% 0.75/0.94      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.75/0.94        sk_D_3)),
% 0.75/0.94      inference('demod', [status(thm)], ['43', '44'])).
% 0.75/0.94  thf(t8_funct_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.75/0.94       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.75/0.94         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.75/0.94           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.75/0.94  thf('46', plain,
% 0.75/0.94      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.75/0.94         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.75/0.94          | ((X26) = (k1_funct_1 @ X25 @ X24))
% 0.75/0.94          | ~ (v1_funct_1 @ X25)
% 0.75/0.94          | ~ (v1_relat_1 @ X25))),
% 0.75/0.94      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.75/0.94  thf('47', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_D_3)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_D_3)
% 0.75/0.94        | ((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.94  thf('48', plain, ((v1_relat_1 @ sk_D_3)),
% 0.75/0.94      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.94  thf('49', plain, ((v1_funct_1 @ sk_D_3)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('50', plain,
% 0.75/0.94      (((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E)))),
% 0.75/0.94      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.75/0.94  thf('51', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 0.75/0.94      inference('demod', [status(thm)], ['40', '50'])).
% 0.75/0.94  thf('52', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['51'])).
% 0.75/0.94  thf('53', plain,
% 0.75/0.94      ((~ (zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ sk_A)
% 0.75/0.94        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.75/0.94      inference('demod', [status(thm)], ['21', '52'])).
% 0.75/0.94  thf('54', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('55', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['51'])).
% 0.75/0.94  thf('56', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D_3 @ 
% 0.75/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['54', '55'])).
% 0.75/0.94  thf('57', plain,
% 0.75/0.94      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.75/0.94         (((X44) != (k1_xboole_0))
% 0.75/0.94          | ((X45) = (k1_xboole_0))
% 0.75/0.94          | ((X46) = (k1_xboole_0))
% 0.75/0.94          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 0.75/0.94          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.94  thf('58', plain,
% 0.75/0.94      (![X45 : $i, X46 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X46 @ 
% 0.75/0.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ k1_xboole_0)))
% 0.75/0.94          | ~ (v1_funct_2 @ X46 @ X45 @ k1_xboole_0)
% 0.75/0.94          | ((X46) = (k1_xboole_0))
% 0.75/0.94          | ((X45) = (k1_xboole_0)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['57'])).
% 0.75/0.94  thf('59', plain,
% 0.75/0.94      ((((sk_A) = (k1_xboole_0))
% 0.75/0.94        | ((sk_D_3) = (k1_xboole_0))
% 0.75/0.94        | ~ (v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['56', '58'])).
% 0.75/0.94  thf('60', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('61', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['51'])).
% 0.75/0.94  thf('62', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0)),
% 0.75/0.94      inference('demod', [status(thm)], ['60', '61'])).
% 0.75/0.94  thf('63', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_3) = (k1_xboole_0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['59', '62'])).
% 0.75/0.94  thf('64', plain,
% 0.75/0.94      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.75/0.94        sk_D_3)),
% 0.75/0.94      inference('demod', [status(thm)], ['43', '44'])).
% 0.75/0.94  thf('65', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.94  thf('66', plain, (~ (v1_xboole_0 @ sk_D_3)),
% 0.75/0.94      inference('sup-', [status(thm)], ['64', '65'])).
% 0.75/0.94  thf('67', plain,
% 0.75/0.94      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['63', '66'])).
% 0.75/0.94  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.75/0.94  thf('68', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.75/0.94      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.94  thf('69', plain,
% 0.75/0.94      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.75/0.94      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.94  thf(t7_ordinal1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.94  thf('70', plain,
% 0.75/0.94      (![X27 : $i, X28 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.75/0.94  thf('71', plain,
% 0.75/0.94      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['69', '70'])).
% 0.75/0.94  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['68', '71'])).
% 0.75/0.94  thf('73', plain, (((sk_A) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['67', '72'])).
% 0.75/0.94  thf('74', plain, (((sk_A) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['67', '72'])).
% 0.75/0.94  thf('75', plain,
% 0.75/0.94      ((~ (zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0)
% 0.75/0.94        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_3)))),
% 0.75/0.94      inference('demod', [status(thm)], ['53', '73', '74'])).
% 0.75/0.94  thf('76', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D_3 @ 
% 0.75/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['54', '55'])).
% 0.75/0.94  thf('77', plain, (((sk_A) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['67', '72'])).
% 0.75/0.94  thf('78', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D_3 @ 
% 0.75/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['76', '77'])).
% 0.75/0.94  thf('79', plain,
% 0.75/0.94      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.75/0.94         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.75/0.94          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.75/0.94          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.94  thf('80', plain,
% 0.75/0.94      (((zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0)
% 0.75/0.94        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('81', plain,
% 0.75/0.94      (![X39 : $i, X40 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.94  thf('82', plain,
% 0.75/0.94      (![X39 : $i, X40 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X39 @ X40) | ((X40) != (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.94  thf('83', plain, (![X39 : $i]: (zip_tseitin_0 @ X39 @ k1_xboole_0)),
% 0.75/0.94      inference('simplify', [status(thm)], ['82'])).
% 0.75/0.94  thf('84', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.75/0.94      inference('sup+', [status(thm)], ['81', '83'])).
% 0.75/0.94  thf('85', plain,
% 0.75/0.94      (((zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.75/0.94        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['23', '24'])).
% 0.75/0.94  thf('86', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ sk_A @ X0)
% 0.75/0.94          | (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['84', '85'])).
% 0.75/0.94  thf('87', plain,
% 0.75/0.94      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.75/0.94        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.75/0.94      inference('demod', [status(thm)], ['17', '20'])).
% 0.75/0.94  thf('88', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['86', '87'])).
% 0.75/0.94  thf('89', plain,
% 0.75/0.94      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.75/0.94      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.94  thf(d5_funct_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.75/0.94           ( ![C:$i]:
% 0.75/0.94             ( ( r2_hidden @ C @ B ) <=>
% 0.75/0.94               ( ?[D:$i]:
% 0.75/0.94                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.75/0.94                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.75/0.94  thf('90', plain,
% 0.75/0.94      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.75/0.94         (((X17) != (k2_relat_1 @ X15))
% 0.75/0.94          | (r2_hidden @ (sk_D_2 @ X18 @ X15) @ (k1_relat_1 @ X15))
% 0.75/0.94          | ~ (r2_hidden @ X18 @ X17)
% 0.75/0.94          | ~ (v1_funct_1 @ X15)
% 0.75/0.94          | ~ (v1_relat_1 @ X15))),
% 0.75/0.94      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.75/0.94  thf('91', plain,
% 0.75/0.94      (![X15 : $i, X18 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X15)
% 0.75/0.94          | ~ (v1_funct_1 @ X15)
% 0.75/0.94          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X15))
% 0.75/0.94          | (r2_hidden @ (sk_D_2 @ X18 @ X15) @ (k1_relat_1 @ X15)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['90'])).
% 0.75/0.94  thf('92', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.75/0.94          | (r2_hidden @ (sk_D_2 @ (sk_B @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.75/0.94             (k1_relat_1 @ X0))
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['89', '91'])).
% 0.75/0.94  thf('93', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.94  thf('94', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.75/0.94          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['92', '93'])).
% 0.75/0.94  thf('95', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ sk_A)
% 0.75/0.94          | (zip_tseitin_0 @ sk_A @ X0)
% 0.75/0.94          | (v1_xboole_0 @ (k2_relat_1 @ sk_D_3))
% 0.75/0.94          | ~ (v1_funct_1 @ sk_D_3)
% 0.75/0.94          | ~ (v1_relat_1 @ sk_D_3))),
% 0.75/0.94      inference('sup-', [status(thm)], ['88', '94'])).
% 0.75/0.94  thf('96', plain, ((v1_funct_1 @ sk_D_3)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('97', plain, ((v1_relat_1 @ sk_D_3)),
% 0.75/0.94      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.94  thf('98', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ sk_A)
% 0.75/0.94          | (zip_tseitin_0 @ sk_A @ X0)
% 0.75/0.94          | (v1_xboole_0 @ (k2_relat_1 @ sk_D_3)))),
% 0.75/0.94      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.75/0.94  thf('99', plain,
% 0.75/0.94      (![X39 : $i, X40 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.94  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['68', '71'])).
% 0.75/0.94  thf('101', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['99', '100'])).
% 0.75/0.94  thf('102', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((v1_xboole_0 @ (k2_relat_1 @ sk_D_3)) | (zip_tseitin_0 @ sk_A @ X0))),
% 0.75/0.94      inference('clc', [status(thm)], ['98', '101'])).
% 0.75/0.94  thf('103', plain,
% 0.75/0.94      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.75/0.94      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.94  thf('104', plain,
% 0.75/0.94      (![X15 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 0.75/0.94         (((X17) != (k2_relat_1 @ X15))
% 0.75/0.94          | (r2_hidden @ X19 @ X17)
% 0.75/0.94          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X15))
% 0.75/0.94          | ((X19) != (k1_funct_1 @ X15 @ X20))
% 0.75/0.94          | ~ (v1_funct_1 @ X15)
% 0.75/0.94          | ~ (v1_relat_1 @ X15))),
% 0.75/0.94      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.75/0.94  thf('105', plain,
% 0.75/0.94      (![X15 : $i, X20 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X15)
% 0.75/0.94          | ~ (v1_funct_1 @ X15)
% 0.75/0.94          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X15))
% 0.75/0.94          | (r2_hidden @ (k1_funct_1 @ X15 @ X20) @ (k2_relat_1 @ X15)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['104'])).
% 0.75/0.94  thf('106', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.75/0.94          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 0.75/0.94             (k2_relat_1 @ X0))
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['103', '105'])).
% 0.75/0.94  thf('107', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.94  thf('108', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.75/0.94          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['106', '107'])).
% 0.75/0.94  thf('109', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ sk_A @ X0)
% 0.75/0.94          | (v1_xboole_0 @ (k1_relat_1 @ sk_D_3))
% 0.75/0.94          | ~ (v1_funct_1 @ sk_D_3)
% 0.75/0.94          | ~ (v1_relat_1 @ sk_D_3))),
% 0.75/0.94      inference('sup-', [status(thm)], ['102', '108'])).
% 0.75/0.94  thf('110', plain, ((v1_funct_1 @ sk_D_3)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('111', plain, ((v1_relat_1 @ sk_D_3)),
% 0.75/0.94      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.94  thf('112', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ sk_A @ X0) | (v1_xboole_0 @ (k1_relat_1 @ sk_D_3)))),
% 0.75/0.94      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.75/0.94  thf('113', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_3))),
% 0.75/0.94      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.94  thf('114', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['112', '113'])).
% 0.75/0.94  thf('115', plain, (((sk_A) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['67', '72'])).
% 0.75/0.94  thf('116', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 0.75/0.94      inference('demod', [status(thm)], ['114', '115'])).
% 0.75/0.94  thf('117', plain, ((zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('demod', [status(thm)], ['80', '116'])).
% 0.75/0.94  thf('118', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_3))),
% 0.75/0.94      inference('demod', [status(thm)], ['75', '117'])).
% 0.75/0.94  thf('119', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['68', '71'])).
% 0.75/0.94  thf('120', plain, ($false),
% 0.75/0.94      inference('demod', [status(thm)], ['14', '118', '119'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
