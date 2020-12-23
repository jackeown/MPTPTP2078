%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WBGP8tOFFx

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:38 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  131 (1335 expanded)
%              Number of leaves         :   37 ( 401 expanded)
%              Depth                    :   21
%              Number of atoms          :  859 (19618 expanded)
%              Number of equality atoms :   65 ( 857 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k7_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k9_relat_1 @ X19 @ X22 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X31: $i] :
      ( ~ ( r2_hidden @ X31 @ sk_A )
      | ~ ( r2_hidden @ X31 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ X7 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['36','46'])).

thf('48',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['19','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 != k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_B_1 = k1_xboole_0 ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('74',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['73','75'])).

thf('77',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['82','85'])).

thf('87',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('88',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['72','88'])).

thf('90',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['67','89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['12','90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WBGP8tOFFx
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:58:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 214 iterations in 0.235s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.47/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.47/0.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.69  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.69  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.69  thf(sk_E_type, type, sk_E: $i).
% 0.47/0.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.69  thf(t115_funct_2, conjecture,
% 0.47/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.69       ( ![E:$i]:
% 0.47/0.69         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.47/0.69              ( ![F:$i]:
% 0.47/0.69                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.47/0.69                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.69            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.69          ( ![E:$i]:
% 0.47/0.69            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.47/0.69                 ( ![F:$i]:
% 0.47/0.69                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.47/0.69                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.47/0.69    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.47/0.69  thf('0', plain,
% 0.47/0.69      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('1', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(redefinition_k7_relset_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.47/0.69  thf('2', plain,
% 0.47/0.69      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.47/0.69          | ((k7_relset_1 @ X20 @ X21 @ X19 @ X22) = (k9_relat_1 @ X19 @ X22)))),
% 0.47/0.69      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.69  thf('3', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.47/0.69           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.69  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.47/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.69  thf(t143_relat_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ C ) =>
% 0.47/0.69       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.47/0.69         ( ?[D:$i]:
% 0.47/0.69           ( ( r2_hidden @ D @ B ) & 
% 0.47/0.69             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.47/0.69             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.47/0.69          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ (k1_relat_1 @ X9))
% 0.47/0.69          | ~ (v1_relat_1 @ X9))),
% 0.47/0.69      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.47/0.69  thf('6', plain,
% 0.47/0.69      ((~ (v1_relat_1 @ sk_D_1)
% 0.47/0.69        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.69  thf('7', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(cc1_relset_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( v1_relat_1 @ C ) ))).
% 0.47/0.69  thf('8', plain,
% 0.47/0.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.69         ((v1_relat_1 @ X13)
% 0.47/0.69          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.47/0.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.69  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf('10', plain,
% 0.47/0.69      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['6', '9'])).
% 0.47/0.69  thf(d1_xboole_0, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.69  thf('11', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.69  thf('12', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.69  thf('13', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(d1_funct_2, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_1, axiom,
% 0.47/0.69    (![C:$i,B:$i,A:$i]:
% 0.47/0.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.69  thf('14', plain,
% 0.47/0.69      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.69         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.47/0.69          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.47/0.69          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.69  thf('15', plain,
% 0.47/0.69      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.47/0.69        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.69  thf('16', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.69  thf('17', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.69         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.47/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.47/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.69  thf('18', plain,
% 0.47/0.69      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.69  thf('19', plain,
% 0.47/0.69      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.47/0.69        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['15', '18'])).
% 0.47/0.69  thf(zf_stmt_2, axiom,
% 0.47/0.69    (![B:$i,A:$i]:
% 0.47/0.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.69       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.69  thf('20', plain,
% 0.47/0.69      (![X23 : $i, X24 : $i]:
% 0.47/0.69         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.69  thf('21', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.69  thf(zf_stmt_5, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.69  thf('22', plain,
% 0.47/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.69         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.47/0.69          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.47/0.69          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.69  thf('23', plain,
% 0.47/0.69      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.47/0.69        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.47/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.69  thf('24', plain,
% 0.47/0.69      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.47/0.69      inference('sup-', [status(thm)], ['20', '23'])).
% 0.47/0.69  thf('25', plain,
% 0.47/0.69      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.47/0.69        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['15', '18'])).
% 0.47/0.69  thf('26', plain,
% 0.47/0.69      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.69  thf('27', plain,
% 0.47/0.69      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['6', '9'])).
% 0.47/0.69  thf('28', plain,
% 0.47/0.69      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.47/0.69        | ((sk_B_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup+', [status(thm)], ['26', '27'])).
% 0.47/0.69  thf('29', plain,
% 0.47/0.69      (![X31 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X31 @ sk_A)
% 0.47/0.69          | ~ (r2_hidden @ X31 @ sk_C)
% 0.47/0.69          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X31)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('30', plain,
% 0.47/0.69      ((((sk_B_1) = (k1_xboole_0))
% 0.47/0.69        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))
% 0.47/0.69        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.47/0.69      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.69  thf('31', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.47/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.69  thf('32', plain,
% 0.47/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.47/0.69          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ X7)
% 0.47/0.69          | ~ (v1_relat_1 @ X9))),
% 0.47/0.69      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.47/0.69  thf('33', plain,
% 0.47/0.69      ((~ (v1_relat_1 @ sk_D_1)
% 0.47/0.69        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.47/0.69      inference('sup-', [status(thm)], ['31', '32'])).
% 0.47/0.69  thf('34', plain, ((v1_relat_1 @ sk_D_1)),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf('35', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.47/0.69      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.69  thf('36', plain,
% 0.47/0.69      ((((sk_B_1) = (k1_xboole_0))
% 0.47/0.69        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.47/0.69      inference('demod', [status(thm)], ['30', '35'])).
% 0.47/0.69  thf('37', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.47/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.69  thf('38', plain,
% 0.47/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.47/0.69          | (r2_hidden @ (k4_tarski @ (sk_D @ X9 @ X7 @ X8) @ X8) @ X9)
% 0.47/0.69          | ~ (v1_relat_1 @ X9))),
% 0.47/0.69      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.47/0.69  thf('39', plain,
% 0.47/0.69      ((~ (v1_relat_1 @ sk_D_1)
% 0.47/0.69        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.47/0.69           sk_D_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.69  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf('41', plain,
% 0.47/0.69      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['39', '40'])).
% 0.47/0.69  thf(t8_funct_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.69       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.47/0.69         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.47/0.69           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.47/0.69  thf('42', plain,
% 0.47/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.69         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.47/0.69          | ((X12) = (k1_funct_1 @ X11 @ X10))
% 0.47/0.69          | ~ (v1_funct_1 @ X11)
% 0.47/0.69          | ~ (v1_relat_1 @ X11))),
% 0.47/0.69      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.47/0.69  thf('43', plain,
% 0.47/0.69      ((~ (v1_relat_1 @ sk_D_1)
% 0.47/0.69        | ~ (v1_funct_1 @ sk_D_1)
% 0.47/0.69        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.69  thf('44', plain, ((v1_relat_1 @ sk_D_1)),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf('45', plain, ((v1_funct_1 @ sk_D_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('46', plain,
% 0.47/0.69      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.47/0.69      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.47/0.69  thf('47', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 0.47/0.69      inference('demod', [status(thm)], ['36', '46'])).
% 0.47/0.69  thf('48', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['47'])).
% 0.47/0.69  thf('49', plain,
% 0.47/0.69      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.69        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['19', '48'])).
% 0.47/0.69  thf('50', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('51', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['47'])).
% 0.47/0.69  thf('52', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D_1 @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['50', '51'])).
% 0.47/0.69  thf('53', plain,
% 0.47/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.69         (((X28) != (k1_xboole_0))
% 0.47/0.69          | ((X29) = (k1_xboole_0))
% 0.47/0.69          | ((X30) = (k1_xboole_0))
% 0.47/0.69          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.47/0.69          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.69  thf('54', plain,
% 0.47/0.69      (![X29 : $i, X30 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X30 @ 
% 0.47/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ k1_xboole_0)))
% 0.47/0.69          | ~ (v1_funct_2 @ X30 @ X29 @ k1_xboole_0)
% 0.47/0.69          | ((X30) = (k1_xboole_0))
% 0.47/0.69          | ((X29) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['53'])).
% 0.47/0.69  thf('55', plain,
% 0.47/0.69      ((((sk_A) = (k1_xboole_0))
% 0.47/0.69        | ((sk_D_1) = (k1_xboole_0))
% 0.47/0.69        | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['52', '54'])).
% 0.47/0.69  thf('56', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('57', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['47'])).
% 0.47/0.69  thf('58', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0)),
% 0.47/0.69      inference('demod', [status(thm)], ['56', '57'])).
% 0.47/0.69  thf('59', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_1) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['55', '58'])).
% 0.47/0.69  thf('60', plain,
% 0.47/0.69      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['39', '40'])).
% 0.47/0.69  thf('61', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.69  thf('62', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.47/0.69      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.69  thf('63', plain,
% 0.47/0.69      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['59', '62'])).
% 0.47/0.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.69  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.69  thf('65', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['63', '64'])).
% 0.47/0.69  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['63', '64'])).
% 0.47/0.69  thf('67', plain,
% 0.47/0.69      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.69        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['49', '65', '66'])).
% 0.47/0.69  thf('68', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D_1 @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['50', '51'])).
% 0.47/0.69  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['63', '64'])).
% 0.47/0.69  thf('70', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D_1 @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['68', '69'])).
% 0.47/0.69  thf('71', plain,
% 0.47/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.69         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.47/0.69          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.47/0.69          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.69  thf('72', plain,
% 0.47/0.69      (((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.69        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['70', '71'])).
% 0.47/0.69  thf('73', plain,
% 0.47/0.69      (![X23 : $i, X24 : $i]:
% 0.47/0.69         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.69  thf('74', plain,
% 0.47/0.69      (![X23 : $i, X24 : $i]:
% 0.47/0.69         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.69  thf('75', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.47/0.69      inference('simplify', [status(thm)], ['74'])).
% 0.47/0.69  thf('76', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.47/0.69      inference('sup+', [status(thm)], ['73', '75'])).
% 0.47/0.69  thf('77', plain,
% 0.47/0.69      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.47/0.69        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.47/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.69  thf('78', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((zip_tseitin_0 @ sk_A @ X0)
% 0.47/0.69          | (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.47/0.69      inference('sup-', [status(thm)], ['76', '77'])).
% 0.47/0.69  thf('79', plain,
% 0.47/0.69      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.47/0.69        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['15', '18'])).
% 0.47/0.69  thf('80', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['78', '79'])).
% 0.47/0.69  thf('81', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.69  thf('82', plain,
% 0.47/0.69      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | (zip_tseitin_0 @ sk_A @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['80', '81'])).
% 0.47/0.69  thf('83', plain,
% 0.47/0.69      (![X23 : $i, X24 : $i]:
% 0.47/0.69         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.69  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.69  thf('85', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.47/0.69      inference('sup+', [status(thm)], ['83', '84'])).
% 0.47/0.69  thf('86', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 0.47/0.69      inference('clc', [status(thm)], ['82', '85'])).
% 0.47/0.69  thf('87', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['63', '64'])).
% 0.47/0.69  thf('88', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 0.47/0.69      inference('demod', [status(thm)], ['86', '87'])).
% 0.47/0.69  thf('89', plain, ((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.69      inference('demod', [status(thm)], ['72', '88'])).
% 0.47/0.69  thf('90', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['67', '89'])).
% 0.47/0.69  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.69  thf('92', plain, ($false),
% 0.47/0.69      inference('demod', [status(thm)], ['12', '90', '91'])).
% 0.47/0.69  
% 0.47/0.69  % SZS output end Refutation
% 0.47/0.69  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
