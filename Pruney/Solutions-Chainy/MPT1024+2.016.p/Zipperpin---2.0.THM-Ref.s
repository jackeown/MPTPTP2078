%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TuULHYjxev

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:36 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  120 (1036 expanded)
%              Number of leaves         :   37 ( 315 expanded)
%              Depth                    :   21
%              Number of atoms          :  825 (15240 expanded)
%              Number of equality atoms :   61 ( 665 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k9_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k9_relat_1 @ X4 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X4 @ X2 @ X3 ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
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

thf('14',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('22',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_A )
      | ~ ( r2_hidden @ X34 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k9_relat_1 @ X4 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X4 @ X2 @ X3 ) @ X2 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('35',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('38',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k9_relat_1 @ X4 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X4 @ X2 @ X3 ) @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('41',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X9 )
      | ( X10
        = ( k1_funct_1 @ X9 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('45',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['36','46'])).

thf('48',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['19','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 != k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('58',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('62',plain,(
    ~ ( r1_tarski @ sk_D_1 @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('65',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('67',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['49','65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('70',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('74',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X27 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,(
    ! [X26: $i] :
      ( zip_tseitin_0 @ X26 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['73','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['76'])).

thf('78',plain,(
    zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['67','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['12','79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TuULHYjxev
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:22:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 138 iterations in 0.130s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.42/0.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.42/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.60  thf(t115_funct_2, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60       ( ![E:$i]:
% 0.42/0.60         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.42/0.60              ( ![F:$i]:
% 0.42/0.60                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.42/0.60                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.60            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60          ( ![E:$i]:
% 0.42/0.60            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.42/0.60                 ( ![F:$i]:
% 0.42/0.60                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.42/0.60                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(redefinition_k7_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.42/0.60          | ((k7_relset_1 @ X23 @ X24 @ X22 @ X25) = (k9_relat_1 @ X22 @ X25)))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.42/0.60           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.60  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.42/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.60  thf(t143_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ C ) =>
% 0.42/0.60       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.42/0.60         ( ?[D:$i]:
% 0.42/0.60           ( ( r2_hidden @ D @ B ) & 
% 0.42/0.60             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.42/0.60             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X3 @ (k9_relat_1 @ X4 @ X2))
% 0.42/0.60          | (r2_hidden @ (sk_D @ X4 @ X2 @ X3) @ (k1_relat_1 @ X4))
% 0.42/0.60          | ~ (v1_relat_1 @ X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ sk_D_1)
% 0.42/0.60        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(cc1_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( v1_relat_1 @ C ) ))).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.60         ((v1_relat_1 @ X13)
% 0.42/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.60  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.42/0.60      inference('demod', [status(thm)], ['6', '9'])).
% 0.42/0.60  thf(t7_ordinal1, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X11 : $i, X12 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.42/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (~ (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (sk_D @ sk_D_1 @ sk_C @ sk_E))),
% 0.42/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.60  thf('13', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(d1_funct_2, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_1, axiom,
% 0.42/0.60    (![C:$i,B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.42/0.60         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.42/0.60          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.42/0.60          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.42/0.60        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.60         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.42/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.42/0.60        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.42/0.60      inference('demod', [status(thm)], ['15', '18'])).
% 0.42/0.60  thf(zf_stmt_2, axiom,
% 0.42/0.60    (![B:$i,A:$i]:
% 0.42/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      (![X26 : $i, X27 : $i]:
% 0.42/0.60         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_5, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.42/0.60         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.42/0.60          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.42/0.60          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.42/0.60        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['20', '23'])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.42/0.60        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.42/0.60      inference('demod', [status(thm)], ['15', '18'])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.42/0.60      inference('demod', [status(thm)], ['6', '9'])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.42/0.60        | ((sk_B) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.42/0.60  thf('29', plain,
% 0.42/0.60      (![X34 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X34 @ sk_A)
% 0.42/0.60          | ~ (r2_hidden @ X34 @ sk_C)
% 0.42/0.60          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X34)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      ((((sk_B) = (k1_xboole_0))
% 0.42/0.60        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))
% 0.42/0.60        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.42/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.60  thf('31', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.42/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X3 @ (k9_relat_1 @ X4 @ X2))
% 0.42/0.60          | (r2_hidden @ (sk_D @ X4 @ X2 @ X3) @ X2)
% 0.42/0.60          | ~ (v1_relat_1 @ X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ sk_D_1)
% 0.42/0.60        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.42/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.60  thf('34', plain, ((v1_relat_1 @ sk_D_1)),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.60  thf('35', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.42/0.60      inference('demod', [status(thm)], ['33', '34'])).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      ((((sk_B) = (k1_xboole_0))
% 0.42/0.60        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.42/0.60      inference('demod', [status(thm)], ['30', '35'])).
% 0.42/0.60  thf('37', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.42/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X3 @ (k9_relat_1 @ X4 @ X2))
% 0.42/0.60          | (r2_hidden @ (k4_tarski @ (sk_D @ X4 @ X2 @ X3) @ X3) @ X4)
% 0.42/0.60          | ~ (v1_relat_1 @ X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.42/0.60  thf('39', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ sk_D_1)
% 0.42/0.60        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.42/0.60           sk_D_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.60  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.42/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.60  thf(t8_funct_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.42/0.60       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.42/0.60         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.42/0.60           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.60         (~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ X9)
% 0.42/0.60          | ((X10) = (k1_funct_1 @ X9 @ X8))
% 0.42/0.60          | ~ (v1_funct_1 @ X9)
% 0.42/0.60          | ~ (v1_relat_1 @ X9))),
% 0.42/0.60      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.42/0.60  thf('43', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ sk_D_1)
% 0.42/0.60        | ~ (v1_funct_1 @ sk_D_1)
% 0.42/0.60        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('44', plain, ((v1_relat_1 @ sk_D_1)),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.60  thf('45', plain, ((v1_funct_1 @ sk_D_1)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('46', plain,
% 0.42/0.60      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.42/0.60      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.42/0.60  thf('47', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 0.42/0.60      inference('demod', [status(thm)], ['36', '46'])).
% 0.42/0.60  thf('48', plain, (((sk_B) = (k1_xboole_0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['47'])).
% 0.42/0.60  thf('49', plain,
% 0.42/0.60      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A)
% 0.42/0.60        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.42/0.60      inference('demod', [status(thm)], ['19', '48'])).
% 0.42/0.60  thf('50', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('51', plain, (((sk_B) = (k1_xboole_0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['47'])).
% 0.42/0.60  thf('52', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['50', '51'])).
% 0.42/0.60  thf('53', plain,
% 0.42/0.60      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.42/0.60         (((X31) != (k1_xboole_0))
% 0.42/0.60          | ((X32) = (k1_xboole_0))
% 0.42/0.60          | ((X33) = (k1_xboole_0))
% 0.42/0.60          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.42/0.60          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.60  thf('54', plain,
% 0.42/0.60      (![X32 : $i, X33 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X33 @ 
% 0.42/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ k1_xboole_0)))
% 0.42/0.60          | ~ (v1_funct_2 @ X33 @ X32 @ k1_xboole_0)
% 0.42/0.60          | ((X33) = (k1_xboole_0))
% 0.42/0.60          | ((X32) = (k1_xboole_0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['53'])).
% 0.42/0.60  thf('55', plain,
% 0.42/0.60      ((((sk_A) = (k1_xboole_0))
% 0.42/0.60        | ((sk_D_1) = (k1_xboole_0))
% 0.42/0.60        | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['52', '54'])).
% 0.42/0.60  thf('56', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('57', plain, (((sk_B) = (k1_xboole_0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['47'])).
% 0.42/0.60  thf('58', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0)),
% 0.42/0.60      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.60  thf('59', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['55', '58'])).
% 0.42/0.60  thf('60', plain,
% 0.42/0.60      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.42/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.60  thf('61', plain,
% 0.42/0.60      (![X11 : $i, X12 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.42/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.60  thf('62', plain,
% 0.42/0.60      (~ (r1_tarski @ sk_D_1 @ 
% 0.42/0.60          (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E))),
% 0.42/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.42/0.60  thf('63', plain,
% 0.42/0.60      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.42/0.60           (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E))
% 0.42/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['59', '62'])).
% 0.42/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.60  thf('64', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.42/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.60  thf('65', plain, (((sk_A) = (k1_xboole_0))),
% 0.42/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.42/0.60  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 0.42/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.42/0.60  thf('67', plain,
% 0.42/0.60      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.42/0.60        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_1)))),
% 0.42/0.60      inference('demod', [status(thm)], ['49', '65', '66'])).
% 0.42/0.60  thf('68', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['50', '51'])).
% 0.42/0.60  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.42/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.42/0.60  thf('70', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['68', '69'])).
% 0.42/0.60  thf('71', plain,
% 0.42/0.60      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.42/0.60         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.42/0.60          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.42/0.60          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.60  thf('72', plain,
% 0.42/0.60      (((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.42/0.60        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.42/0.60  thf('73', plain,
% 0.42/0.60      (![X26 : $i, X27 : $i]:
% 0.42/0.60         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.60  thf('74', plain,
% 0.42/0.60      (![X26 : $i, X27 : $i]:
% 0.42/0.60         ((zip_tseitin_0 @ X26 @ X27) | ((X27) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.60  thf('75', plain, (![X26 : $i]: (zip_tseitin_0 @ X26 @ k1_xboole_0)),
% 0.42/0.60      inference('simplify', [status(thm)], ['74'])).
% 0.42/0.60  thf('76', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.42/0.60      inference('sup+', [status(thm)], ['73', '75'])).
% 0.42/0.60  thf('77', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.42/0.60      inference('eq_fact', [status(thm)], ['76'])).
% 0.42/0.60  thf('78', plain, ((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.42/0.60      inference('demod', [status(thm)], ['72', '77'])).
% 0.42/0.60  thf('79', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_1))),
% 0.42/0.60      inference('demod', [status(thm)], ['67', '78'])).
% 0.42/0.60  thf('80', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.42/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.60  thf('81', plain, ($false),
% 0.42/0.60      inference('demod', [status(thm)], ['12', '79', '80'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
