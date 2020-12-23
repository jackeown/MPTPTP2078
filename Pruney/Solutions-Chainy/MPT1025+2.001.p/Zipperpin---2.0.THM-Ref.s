%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eg4EvZTvCH

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:42 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 302 expanded)
%              Number of leaves         :   49 ( 112 expanded)
%              Depth                    :   18
%              Number of atoms          : 1055 (3335 expanded)
%              Number of equality atoms :   60 ( 151 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X22 @ X20 @ X21 ) @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ),
    inference(demod,[status(thm)],['6','9'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ X24 )
      | ( X25
        = ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('14',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D_2 @ X22 @ X20 @ X21 ) @ X20 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X47: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_3 @ X47 ) )
      | ~ ( r2_hidden @ X47 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X47 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D_2 @ X22 @ X20 @ X21 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('27',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('29',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ),
    inference(demod,[status(thm)],['6','9'])).

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

thf('31',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X6 ) @ X6 )
      | ( X8
       != ( k3_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('36',plain,(
    ! [X6: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X9 @ X6 ) @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k3_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('48',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k3_tarski @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('55',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('56',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k3_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('60',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('67',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('68',plain,(
    r2_hidden @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('70',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k3_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('71',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k3_tarski @ X6 ) )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,
    ( ( r2_hidden @ ( sk_B @ sk_D_3 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['68','72'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('74',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('75',plain,
    ( ( r2_hidden @ ( sk_B @ sk_D_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('76',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X36 ) @ X38 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_D_3 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ sk_D_3 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_D_3 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['63','79'])).

thf('81',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_D_3 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) )
    | ( sk_D_3
      = ( k3_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['58','82'])).

thf('84',plain,
    ( ( sk_D_3
      = ( k3_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('86',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('87',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('94',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ ( k1_mcart_1 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('96',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['85','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_3 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_3 ) )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_3 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_3 ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['30','101'])).

thf('103',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference(demod,[status(thm)],['29','102'])).

thf('104',plain,(
    sk_E
 != ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['22','103'])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eg4EvZTvCH
% 0.13/0.38  % Computer   : n023.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 13:15:06 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 1.18/1.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.18/1.37  % Solved by: fo/fo7.sh
% 1.18/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.37  % done 881 iterations in 0.888s
% 1.18/1.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.18/1.37  % SZS output start Refutation
% 1.18/1.37  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.18/1.37  thf(sk_B_type, type, sk_B: $i > $i).
% 1.18/1.37  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.18/1.37  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.18/1.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.37  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.18/1.37  thf(sk_E_type, type, sk_E: $i).
% 1.18/1.37  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.18/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.37  thf(sk_D_3_type, type, sk_D_3: $i).
% 1.18/1.37  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 1.18/1.37  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.18/1.37  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.18/1.37  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.18/1.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.18/1.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.37  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.18/1.37  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.18/1.37  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.18/1.37  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.18/1.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.18/1.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.18/1.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.18/1.37  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.18/1.37  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.18/1.37  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.18/1.37  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.18/1.37  thf(t116_funct_2, conjecture,
% 1.18/1.37    (![A:$i,B:$i,C:$i,D:$i]:
% 1.18/1.37     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.18/1.37         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.37       ( ![E:$i]:
% 1.18/1.37         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.18/1.37              ( ![F:$i]:
% 1.18/1.37                ( ( m1_subset_1 @ F @ A ) =>
% 1.18/1.37                  ( ~( ( r2_hidden @ F @ C ) & 
% 1.18/1.37                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 1.18/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.37    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.18/1.37        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.18/1.37            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.37          ( ![E:$i]:
% 1.18/1.37            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.18/1.37                 ( ![F:$i]:
% 1.18/1.37                   ( ( m1_subset_1 @ F @ A ) =>
% 1.18/1.37                     ( ~( ( r2_hidden @ F @ C ) & 
% 1.18/1.37                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 1.18/1.37    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 1.18/1.37  thf('0', plain,
% 1.18/1.37      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ sk_C_1))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('1', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf(redefinition_k7_relset_1, axiom,
% 1.18/1.37    (![A:$i,B:$i,C:$i,D:$i]:
% 1.18/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.37       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.18/1.37  thf('2', plain,
% 1.18/1.37      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.18/1.37         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.18/1.37          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 1.18/1.37      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.18/1.37  thf('3', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ X0)
% 1.18/1.37           = (k9_relat_1 @ sk_D_3 @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['1', '2'])).
% 1.18/1.37  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 1.18/1.37      inference('demod', [status(thm)], ['0', '3'])).
% 1.18/1.37  thf(t143_relat_1, axiom,
% 1.18/1.37    (![A:$i,B:$i,C:$i]:
% 1.18/1.37     ( ( v1_relat_1 @ C ) =>
% 1.18/1.37       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.18/1.37         ( ?[D:$i]:
% 1.18/1.37           ( ( r2_hidden @ D @ B ) & 
% 1.18/1.37             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.18/1.37             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.18/1.37  thf('5', plain,
% 1.18/1.37      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.37         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 1.18/1.37          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X22 @ X20 @ X21) @ X21) @ X22)
% 1.18/1.37          | ~ (v1_relat_1 @ X22))),
% 1.18/1.37      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.18/1.37  thf('6', plain,
% 1.18/1.37      ((~ (v1_relat_1 @ sk_D_3)
% 1.18/1.37        | (r2_hidden @ 
% 1.18/1.37           (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ sk_D_3))),
% 1.18/1.37      inference('sup-', [status(thm)], ['4', '5'])).
% 1.18/1.37  thf('7', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf(cc1_relset_1, axiom,
% 1.18/1.37    (![A:$i,B:$i,C:$i]:
% 1.18/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.37       ( v1_relat_1 @ C ) ))).
% 1.18/1.37  thf('8', plain,
% 1.18/1.37      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.18/1.37         ((v1_relat_1 @ X26)
% 1.18/1.37          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.18/1.37      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.18/1.37  thf('9', plain, ((v1_relat_1 @ sk_D_3)),
% 1.18/1.37      inference('sup-', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('10', plain,
% 1.18/1.37      ((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 1.18/1.37        sk_D_3)),
% 1.18/1.37      inference('demod', [status(thm)], ['6', '9'])).
% 1.18/1.37  thf(t8_funct_1, axiom,
% 1.18/1.37    (![A:$i,B:$i,C:$i]:
% 1.18/1.37     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.18/1.37       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.18/1.37         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.18/1.37           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.18/1.37  thf('11', plain,
% 1.18/1.37      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.18/1.37         (~ (r2_hidden @ (k4_tarski @ X23 @ X25) @ X24)
% 1.18/1.37          | ((X25) = (k1_funct_1 @ X24 @ X23))
% 1.18/1.37          | ~ (v1_funct_1 @ X24)
% 1.18/1.37          | ~ (v1_relat_1 @ X24))),
% 1.18/1.37      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.18/1.37  thf('12', plain,
% 1.18/1.37      ((~ (v1_relat_1 @ sk_D_3)
% 1.18/1.37        | ~ (v1_funct_1 @ sk_D_3)
% 1.18/1.37        | ((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 1.18/1.37      inference('sup-', [status(thm)], ['10', '11'])).
% 1.18/1.37  thf('13', plain, ((v1_relat_1 @ sk_D_3)),
% 1.18/1.37      inference('sup-', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('14', plain, ((v1_funct_1 @ sk_D_3)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('15', plain,
% 1.18/1.37      (((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E)))),
% 1.18/1.37      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.18/1.37  thf('16', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 1.18/1.37      inference('demod', [status(thm)], ['0', '3'])).
% 1.18/1.37  thf('17', plain,
% 1.18/1.37      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.37         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 1.18/1.37          | (r2_hidden @ (sk_D_2 @ X22 @ X20 @ X21) @ X20)
% 1.18/1.37          | ~ (v1_relat_1 @ X22))),
% 1.18/1.37      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.18/1.37  thf('18', plain,
% 1.18/1.37      ((~ (v1_relat_1 @ sk_D_3)
% 1.18/1.37        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 1.18/1.37      inference('sup-', [status(thm)], ['16', '17'])).
% 1.18/1.37  thf('19', plain, ((v1_relat_1 @ sk_D_3)),
% 1.18/1.37      inference('sup-', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('20', plain, ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 1.18/1.37      inference('demod', [status(thm)], ['18', '19'])).
% 1.18/1.37  thf('21', plain,
% 1.18/1.37      (![X47 : $i]:
% 1.18/1.37         (((sk_E) != (k1_funct_1 @ sk_D_3 @ X47))
% 1.18/1.37          | ~ (r2_hidden @ X47 @ sk_C_1)
% 1.18/1.37          | ~ (m1_subset_1 @ X47 @ sk_A))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('22', plain,
% 1.18/1.37      ((~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A)
% 1.18/1.37        | ((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 1.18/1.37      inference('sup-', [status(thm)], ['20', '21'])).
% 1.18/1.37  thf('23', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 1.18/1.37      inference('demod', [status(thm)], ['0', '3'])).
% 1.18/1.37  thf('24', plain,
% 1.18/1.37      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.37         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 1.18/1.37          | (r2_hidden @ (sk_D_2 @ X22 @ X20 @ X21) @ (k1_relat_1 @ X22))
% 1.18/1.37          | ~ (v1_relat_1 @ X22))),
% 1.18/1.37      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.18/1.37  thf('25', plain,
% 1.18/1.37      ((~ (v1_relat_1 @ sk_D_3)
% 1.18/1.37        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ 
% 1.18/1.37           (k1_relat_1 @ sk_D_3)))),
% 1.18/1.37      inference('sup-', [status(thm)], ['23', '24'])).
% 1.18/1.37  thf('26', plain, ((v1_relat_1 @ sk_D_3)),
% 1.18/1.37      inference('sup-', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('27', plain,
% 1.18/1.37      ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 1.18/1.37      inference('demod', [status(thm)], ['25', '26'])).
% 1.18/1.37  thf(t1_subset, axiom,
% 1.18/1.37    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.18/1.37  thf('28', plain,
% 1.18/1.37      (![X14 : $i, X15 : $i]:
% 1.18/1.37         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 1.18/1.37      inference('cnf', [status(esa)], [t1_subset])).
% 1.18/1.37  thf('29', plain,
% 1.18/1.37      ((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 1.18/1.37      inference('sup-', [status(thm)], ['27', '28'])).
% 1.18/1.37  thf('30', plain,
% 1.18/1.37      ((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 1.18/1.37        sk_D_3)),
% 1.18/1.37      inference('demod', [status(thm)], ['6', '9'])).
% 1.18/1.37  thf(d1_funct_2, axiom,
% 1.18/1.37    (![A:$i,B:$i,C:$i]:
% 1.18/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.37       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.37           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.18/1.37             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.18/1.37         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.37           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.18/1.37             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.18/1.37  thf(zf_stmt_1, axiom,
% 1.18/1.37    (![B:$i,A:$i]:
% 1.18/1.37     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.37       ( zip_tseitin_0 @ B @ A ) ))).
% 1.18/1.37  thf('31', plain,
% 1.18/1.37      (![X39 : $i, X40 : $i]:
% 1.18/1.37         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.18/1.37  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.18/1.37  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.18/1.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.18/1.37  thf('33', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.18/1.37      inference('sup+', [status(thm)], ['31', '32'])).
% 1.18/1.37  thf(d1_xboole_0, axiom,
% 1.18/1.37    (![A:$i]:
% 1.18/1.37     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.18/1.37  thf('34', plain,
% 1.18/1.37      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.18/1.37      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.37  thf(d4_tarski, axiom,
% 1.18/1.37    (![A:$i,B:$i]:
% 1.18/1.37     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 1.18/1.37       ( ![C:$i]:
% 1.18/1.37         ( ( r2_hidden @ C @ B ) <=>
% 1.18/1.37           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 1.18/1.37  thf('35', plain,
% 1.18/1.37      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.18/1.37         (~ (r2_hidden @ X9 @ X8)
% 1.18/1.37          | (r2_hidden @ (sk_D_1 @ X9 @ X6) @ X6)
% 1.18/1.37          | ((X8) != (k3_tarski @ X6)))),
% 1.18/1.37      inference('cnf', [status(esa)], [d4_tarski])).
% 1.18/1.37  thf('36', plain,
% 1.18/1.37      (![X6 : $i, X9 : $i]:
% 1.18/1.37         ((r2_hidden @ (sk_D_1 @ X9 @ X6) @ X6)
% 1.18/1.37          | ~ (r2_hidden @ X9 @ (k3_tarski @ X6)))),
% 1.18/1.37      inference('simplify', [status(thm)], ['35'])).
% 1.18/1.37  thf('37', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v1_xboole_0 @ (k3_tarski @ X0))
% 1.18/1.37          | (r2_hidden @ (sk_D_1 @ (sk_B @ (k3_tarski @ X0)) @ X0) @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['34', '36'])).
% 1.18/1.37  thf('38', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.18/1.37      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.37  thf('39', plain,
% 1.18/1.37      (![X0 : $i]: ((v1_xboole_0 @ (k3_tarski @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['37', '38'])).
% 1.18/1.37  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.18/1.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.18/1.37  thf(t8_boole, axiom,
% 1.18/1.37    (![A:$i,B:$i]:
% 1.18/1.37     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.18/1.37  thf('41', plain,
% 1.18/1.37      (![X3 : $i, X4 : $i]:
% 1.18/1.37         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 1.18/1.37      inference('cnf', [status(esa)], [t8_boole])).
% 1.18/1.37  thf('42', plain,
% 1.18/1.37      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['40', '41'])).
% 1.18/1.37  thf('43', plain,
% 1.18/1.37      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k3_tarski @ X0)))),
% 1.18/1.37      inference('sup-', [status(thm)], ['39', '42'])).
% 1.18/1.37  thf('44', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((zip_tseitin_0 @ X0 @ X1) | ((k1_xboole_0) = (k3_tarski @ X0)))),
% 1.18/1.37      inference('sup-', [status(thm)], ['33', '43'])).
% 1.18/1.37  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.18/1.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.18/1.37  thf('46', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((v1_xboole_0 @ (k3_tarski @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 1.18/1.37      inference('sup+', [status(thm)], ['44', '45'])).
% 1.18/1.37  thf('47', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.18/1.37  thf(zf_stmt_3, axiom,
% 1.18/1.37    (![C:$i,B:$i,A:$i]:
% 1.18/1.37     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.18/1.37       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.18/1.37  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.18/1.37  thf(zf_stmt_5, axiom,
% 1.18/1.37    (![A:$i,B:$i,C:$i]:
% 1.18/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.37       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.18/1.37         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.37           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.18/1.37             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.18/1.37  thf('48', plain,
% 1.18/1.37      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.18/1.37         (~ (zip_tseitin_0 @ X44 @ X45)
% 1.18/1.37          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 1.18/1.37          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.18/1.37  thf('49', plain,
% 1.18/1.37      (((zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 1.18/1.37        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.18/1.37      inference('sup-', [status(thm)], ['47', '48'])).
% 1.18/1.37  thf('50', plain,
% 1.18/1.37      (((v1_xboole_0 @ (k3_tarski @ sk_B_1))
% 1.18/1.37        | (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A))),
% 1.18/1.37      inference('sup-', [status(thm)], ['46', '49'])).
% 1.18/1.37  thf('51', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('52', plain,
% 1.18/1.37      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.18/1.37         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.18/1.37          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 1.18/1.37          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.18/1.37  thf('53', plain,
% 1.18/1.37      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 1.18/1.37        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3)))),
% 1.18/1.37      inference('sup-', [status(thm)], ['51', '52'])).
% 1.18/1.37  thf('54', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf(redefinition_k1_relset_1, axiom,
% 1.18/1.37    (![A:$i,B:$i,C:$i]:
% 1.18/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.37       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.18/1.37  thf('55', plain,
% 1.18/1.37      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.18/1.37         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 1.18/1.37          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.18/1.37      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.18/1.37  thf('56', plain,
% 1.18/1.37      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 1.18/1.37      inference('sup-', [status(thm)], ['54', '55'])).
% 1.18/1.37  thf('57', plain,
% 1.18/1.37      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 1.18/1.37        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.18/1.37      inference('demod', [status(thm)], ['53', '56'])).
% 1.18/1.37  thf('58', plain,
% 1.18/1.37      (((v1_xboole_0 @ (k3_tarski @ sk_B_1)) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.18/1.37      inference('sup-', [status(thm)], ['50', '57'])).
% 1.18/1.37  thf('59', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.18/1.37      inference('sup+', [status(thm)], ['31', '32'])).
% 1.18/1.37  thf('60', plain,
% 1.18/1.37      (((zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 1.18/1.37        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.18/1.37      inference('sup-', [status(thm)], ['47', '48'])).
% 1.18/1.37  thf('61', plain,
% 1.18/1.37      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A))),
% 1.18/1.37      inference('sup-', [status(thm)], ['59', '60'])).
% 1.18/1.37  thf('62', plain,
% 1.18/1.37      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 1.18/1.37        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.18/1.37      inference('demod', [status(thm)], ['53', '56'])).
% 1.18/1.37  thf('63', plain,
% 1.18/1.37      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.18/1.37      inference('sup-', [status(thm)], ['61', '62'])).
% 1.18/1.37  thf('64', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf(t2_subset, axiom,
% 1.18/1.37    (![A:$i,B:$i]:
% 1.18/1.37     ( ( m1_subset_1 @ A @ B ) =>
% 1.18/1.37       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.18/1.37  thf('65', plain,
% 1.18/1.37      (![X16 : $i, X17 : $i]:
% 1.18/1.37         ((r2_hidden @ X16 @ X17)
% 1.18/1.37          | (v1_xboole_0 @ X17)
% 1.18/1.37          | ~ (m1_subset_1 @ X16 @ X17))),
% 1.18/1.37      inference('cnf', [status(esa)], [t2_subset])).
% 1.18/1.37  thf('66', plain,
% 1.18/1.37      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 1.18/1.37        | (r2_hidden @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 1.18/1.37      inference('sup-', [status(thm)], ['64', '65'])).
% 1.18/1.37  thf(fc1_subset_1, axiom,
% 1.18/1.37    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.18/1.37  thf('67', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 1.18/1.37      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.18/1.37  thf('68', plain,
% 1.18/1.37      ((r2_hidden @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.18/1.37      inference('clc', [status(thm)], ['66', '67'])).
% 1.18/1.37  thf('69', plain,
% 1.18/1.37      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.18/1.37      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.37  thf('70', plain,
% 1.18/1.37      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.18/1.37         (~ (r2_hidden @ X5 @ X6)
% 1.18/1.37          | ~ (r2_hidden @ X7 @ X5)
% 1.18/1.37          | (r2_hidden @ X7 @ X8)
% 1.18/1.37          | ((X8) != (k3_tarski @ X6)))),
% 1.18/1.37      inference('cnf', [status(esa)], [d4_tarski])).
% 1.18/1.37  thf('71', plain,
% 1.18/1.37      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.18/1.37         ((r2_hidden @ X7 @ (k3_tarski @ X6))
% 1.18/1.37          | ~ (r2_hidden @ X7 @ X5)
% 1.18/1.37          | ~ (r2_hidden @ X5 @ X6))),
% 1.18/1.37      inference('simplify', [status(thm)], ['70'])).
% 1.18/1.37  thf('72', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((v1_xboole_0 @ X0)
% 1.18/1.37          | ~ (r2_hidden @ X0 @ X1)
% 1.18/1.37          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 1.18/1.37      inference('sup-', [status(thm)], ['69', '71'])).
% 1.18/1.37  thf('73', plain,
% 1.18/1.37      (((r2_hidden @ (sk_B @ sk_D_3) @ 
% 1.18/1.37         (k3_tarski @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 1.18/1.37        | (v1_xboole_0 @ sk_D_3))),
% 1.18/1.37      inference('sup-', [status(thm)], ['68', '72'])).
% 1.18/1.37  thf(t99_zfmisc_1, axiom,
% 1.18/1.37    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 1.18/1.37  thf('74', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 1.18/1.37      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 1.18/1.37  thf('75', plain,
% 1.18/1.37      (((r2_hidden @ (sk_B @ sk_D_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.18/1.37        | (v1_xboole_0 @ sk_D_3))),
% 1.18/1.37      inference('demod', [status(thm)], ['73', '74'])).
% 1.18/1.37  thf(t10_mcart_1, axiom,
% 1.18/1.37    (![A:$i,B:$i,C:$i]:
% 1.18/1.37     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.18/1.37       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.18/1.37         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.18/1.37  thf('76', plain,
% 1.18/1.37      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.18/1.37         ((r2_hidden @ (k2_mcart_1 @ X36) @ X38)
% 1.18/1.37          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 1.18/1.37      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.18/1.37  thf('77', plain,
% 1.18/1.37      (((v1_xboole_0 @ sk_D_3)
% 1.18/1.37        | (r2_hidden @ (k2_mcart_1 @ (sk_B @ sk_D_3)) @ sk_B_1))),
% 1.18/1.37      inference('sup-', [status(thm)], ['75', '76'])).
% 1.18/1.37  thf('78', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.18/1.37      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.37  thf('79', plain, (((v1_xboole_0 @ sk_D_3) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.18/1.37      inference('sup-', [status(thm)], ['77', '78'])).
% 1.18/1.37  thf('80', plain,
% 1.18/1.37      ((((sk_A) = (k1_relat_1 @ sk_D_3)) | (v1_xboole_0 @ sk_D_3))),
% 1.18/1.37      inference('sup-', [status(thm)], ['63', '79'])).
% 1.18/1.37  thf('81', plain,
% 1.18/1.37      (![X3 : $i, X4 : $i]:
% 1.18/1.37         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 1.18/1.37      inference('cnf', [status(esa)], [t8_boole])).
% 1.18/1.37  thf('82', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (((sk_A) = (k1_relat_1 @ sk_D_3))
% 1.18/1.37          | ((sk_D_3) = (X0))
% 1.18/1.37          | ~ (v1_xboole_0 @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['80', '81'])).
% 1.18/1.37  thf('83', plain,
% 1.18/1.37      ((((sk_A) = (k1_relat_1 @ sk_D_3))
% 1.18/1.37        | ((sk_D_3) = (k3_tarski @ sk_B_1))
% 1.18/1.37        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.18/1.37      inference('sup-', [status(thm)], ['58', '82'])).
% 1.18/1.37  thf('84', plain,
% 1.18/1.37      ((((sk_D_3) = (k3_tarski @ sk_B_1)) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.18/1.37      inference('simplify', [status(thm)], ['83'])).
% 1.18/1.37  thf('85', plain,
% 1.18/1.37      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k3_tarski @ X0)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['39', '42'])).
% 1.18/1.38  thf('86', plain,
% 1.18/1.38      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.18/1.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.38  thf('87', plain,
% 1.18/1.38      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.18/1.38         ((r2_hidden @ (k1_mcart_1 @ X36) @ X37)
% 1.18/1.38          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 1.18/1.38      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.18/1.38  thf('88', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.18/1.38          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 1.18/1.38      inference('sup-', [status(thm)], ['86', '87'])).
% 1.18/1.38  thf('89', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.18/1.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.38  thf('90', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['88', '89'])).
% 1.18/1.38  thf('91', plain,
% 1.18/1.38      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['40', '41'])).
% 1.18/1.38  thf('92', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['90', '91'])).
% 1.18/1.38  thf('93', plain,
% 1.18/1.38      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.18/1.38         ((r2_hidden @ (k1_mcart_1 @ X36) @ X37)
% 1.18/1.38          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 1.18/1.38      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.18/1.38  thf('94', plain,
% 1.18/1.38      (![X1 : $i, X2 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X2 @ k1_xboole_0)
% 1.18/1.38          | ~ (v1_xboole_0 @ X1)
% 1.18/1.38          | (r2_hidden @ (k1_mcart_1 @ X2) @ X1))),
% 1.18/1.38      inference('sup-', [status(thm)], ['92', '93'])).
% 1.18/1.38  thf('95', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.18/1.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.38  thf('96', plain,
% 1.18/1.38      (![X1 : $i, X2 : $i]:
% 1.18/1.38         (~ (v1_xboole_0 @ X1) | ~ (r2_hidden @ X2 @ k1_xboole_0))),
% 1.18/1.38      inference('clc', [status(thm)], ['94', '95'])).
% 1.18/1.38  thf('97', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X1 @ (k3_tarski @ X0))
% 1.18/1.38          | ~ (v1_xboole_0 @ X0)
% 1.18/1.38          | ~ (v1_xboole_0 @ X2))),
% 1.18/1.38      inference('sup-', [status(thm)], ['85', '96'])).
% 1.18/1.38  thf('98', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X1 @ (k3_tarski @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('condensation', [status(thm)], ['97'])).
% 1.18/1.38  thf('99', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X0 @ sk_D_3)
% 1.18/1.38          | ((sk_A) = (k1_relat_1 @ sk_D_3))
% 1.18/1.38          | ~ (v1_xboole_0 @ sk_B_1))),
% 1.18/1.38      inference('sup-', [status(thm)], ['84', '98'])).
% 1.18/1.38  thf('100', plain,
% 1.18/1.38      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['61', '62'])).
% 1.18/1.38  thf('101', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (((sk_A) = (k1_relat_1 @ sk_D_3)) | ~ (r2_hidden @ X0 @ sk_D_3))),
% 1.18/1.38      inference('clc', [status(thm)], ['99', '100'])).
% 1.18/1.38  thf('102', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 1.18/1.38      inference('sup-', [status(thm)], ['30', '101'])).
% 1.18/1.38  thf('103', plain, ((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A)),
% 1.18/1.38      inference('demod', [status(thm)], ['29', '102'])).
% 1.18/1.38  thf('104', plain,
% 1.18/1.38      (((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E)))),
% 1.18/1.38      inference('demod', [status(thm)], ['22', '103'])).
% 1.18/1.38  thf('105', plain, ($false),
% 1.18/1.38      inference('simplify_reflect-', [status(thm)], ['15', '104'])).
% 1.18/1.38  
% 1.18/1.38  % SZS output end Refutation
% 1.18/1.38  
% 1.18/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
