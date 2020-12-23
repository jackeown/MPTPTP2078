%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lUCKcTMuEu

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:49 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 169 expanded)
%              Number of leaves         :   42 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  704 (2084 expanded)
%              Number of equality atoms :   37 (  83 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k7_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k9_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X18
       != ( k9_relat_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X19 @ X15 @ X16 ) @ X19 @ X15 @ X16 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X19 @ X15 @ X16 ) @ X19 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ X12 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X41: $i] :
      ( ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X41 ) )
      | ~ ( r2_hidden @ X41 @ sk_C )
      | ~ ( m1_subset_1 @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X11
        = ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
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

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('28',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_1 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_1 @ X38 @ X39 )
      | ( zip_tseitin_2 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('33',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_2 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('37',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['27','48'])).

thf('50',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['26','49'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('52',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['23','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lUCKcTMuEu
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.73  % Solved by: fo/fo7.sh
% 0.56/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.73  % done 173 iterations in 0.277s
% 0.56/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.73  % SZS output start Refutation
% 0.56/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.56/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.56/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.56/0.73  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.56/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.56/0.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.56/0.73  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.56/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.73  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.56/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.56/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.56/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.56/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.74  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.56/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.56/0.74  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.56/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.74  thf(t116_funct_2, conjecture,
% 0.56/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.56/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.74       ( ![E:$i]:
% 0.56/0.74         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.56/0.74              ( ![F:$i]:
% 0.56/0.74                ( ( m1_subset_1 @ F @ A ) =>
% 0.56/0.74                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.56/0.74                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.56/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.74        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.56/0.74            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.74          ( ![E:$i]:
% 0.56/0.74            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.56/0.74                 ( ![F:$i]:
% 0.56/0.74                   ( ( m1_subset_1 @ F @ A ) =>
% 0.56/0.74                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.56/0.74                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.56/0.74    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.56/0.74  thf('0', plain,
% 0.56/0.74      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('1', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(redefinition_k7_relset_1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.74       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.56/0.74  thf('2', plain,
% 0.56/0.74      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.56/0.74          | ((k7_relset_1 @ X30 @ X31 @ X29 @ X32) = (k9_relat_1 @ X29 @ X32)))),
% 0.56/0.74      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.56/0.74  thf('3', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.56/0.74           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.56/0.74  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.56/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.56/0.74  thf(d12_funct_1, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.56/0.74       ( ![B:$i,C:$i]:
% 0.56/0.74         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.56/0.74           ( ![D:$i]:
% 0.56/0.74             ( ( r2_hidden @ D @ C ) <=>
% 0.56/0.74               ( ?[E:$i]:
% 0.56/0.74                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.56/0.74                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.56/0.74  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.56/0.74  thf(zf_stmt_2, axiom,
% 0.56/0.74    (![E:$i,D:$i,B:$i,A:$i]:
% 0.56/0.74     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.56/0.74       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.56/0.74         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.56/0.74  thf(zf_stmt_3, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.56/0.74       ( ![B:$i,C:$i]:
% 0.56/0.74         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.56/0.74           ( ![D:$i]:
% 0.56/0.74             ( ( r2_hidden @ D @ C ) <=>
% 0.56/0.74               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.56/0.74  thf('5', plain,
% 0.56/0.74      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.56/0.74         (((X18) != (k9_relat_1 @ X16 @ X15))
% 0.56/0.74          | (zip_tseitin_0 @ (sk_E_1 @ X19 @ X15 @ X16) @ X19 @ X15 @ X16)
% 0.56/0.74          | ~ (r2_hidden @ X19 @ X18)
% 0.56/0.74          | ~ (v1_funct_1 @ X16)
% 0.56/0.74          | ~ (v1_relat_1 @ X16))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.56/0.74  thf('6', plain,
% 0.56/0.74      (![X15 : $i, X16 : $i, X19 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X16)
% 0.56/0.74          | ~ (v1_funct_1 @ X16)
% 0.56/0.74          | ~ (r2_hidden @ X19 @ (k9_relat_1 @ X16 @ X15))
% 0.56/0.74          | (zip_tseitin_0 @ (sk_E_1 @ X19 @ X15 @ X16) @ X19 @ X15 @ X16))),
% 0.56/0.74      inference('simplify', [status(thm)], ['5'])).
% 0.56/0.74  thf('7', plain,
% 0.56/0.74      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.56/0.74         sk_D_1)
% 0.56/0.74        | ~ (v1_funct_1 @ sk_D_1)
% 0.56/0.74        | ~ (v1_relat_1 @ sk_D_1))),
% 0.56/0.74      inference('sup-', [status(thm)], ['4', '6'])).
% 0.56/0.74  thf('8', plain, ((v1_funct_1 @ sk_D_1)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('9', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(cc2_relat_1, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( v1_relat_1 @ A ) =>
% 0.56/0.74       ( ![B:$i]:
% 0.56/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.56/0.74  thf('10', plain,
% 0.56/0.74      (![X5 : $i, X6 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.56/0.74          | (v1_relat_1 @ X5)
% 0.56/0.74          | ~ (v1_relat_1 @ X6))),
% 0.56/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.56/0.74  thf('11', plain,
% 0.56/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.56/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.56/0.74  thf(fc6_relat_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.56/0.74  thf('12', plain,
% 0.56/0.74      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.56/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.56/0.74  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.56/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.56/0.74  thf('14', plain,
% 0.56/0.74      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.56/0.74        sk_D_1)),
% 0.56/0.74      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.56/0.74  thf('15', plain,
% 0.56/0.74      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.56/0.74         ((r2_hidden @ X10 @ X12) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.56/0.74  thf('16', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)),
% 0.56/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.56/0.74  thf('17', plain,
% 0.56/0.74      (![X41 : $i]:
% 0.56/0.74         (((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X41))
% 0.56/0.74          | ~ (r2_hidden @ X41 @ sk_C)
% 0.56/0.74          | ~ (m1_subset_1 @ X41 @ sk_A))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('18', plain,
% 0.56/0.74      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)
% 0.56/0.74        | ((sk_E_2)
% 0.56/0.74            != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1))))),
% 0.56/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.56/0.74  thf('19', plain,
% 0.56/0.74      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.56/0.74        sk_D_1)),
% 0.56/0.74      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.56/0.74  thf('20', plain,
% 0.56/0.74      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.56/0.74         (((X11) = (k1_funct_1 @ X9 @ X10))
% 0.56/0.74          | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.56/0.74  thf('21', plain,
% 0.56/0.74      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['19', '20'])).
% 0.56/0.74  thf('22', plain,
% 0.56/0.74      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)
% 0.56/0.74        | ((sk_E_2) != (sk_E_2)))),
% 0.56/0.74      inference('demod', [status(thm)], ['18', '21'])).
% 0.56/0.74  thf('23', plain,
% 0.56/0.74      (~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.56/0.74      inference('simplify', [status(thm)], ['22'])).
% 0.56/0.74  thf('24', plain,
% 0.56/0.74      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.56/0.74        sk_D_1)),
% 0.56/0.74      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.56/0.74  thf('25', plain,
% 0.56/0.74      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.56/0.74         ((r2_hidden @ X10 @ (k1_relat_1 @ X9))
% 0.56/0.74          | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.56/0.74  thf('26', plain,
% 0.56/0.74      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.56/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.56/0.74  thf('27', plain,
% 0.56/0.74      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(d1_funct_2, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.56/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.56/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.56/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.56/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.56/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.56/0.74  thf(zf_stmt_4, axiom,
% 0.56/0.74    (![B:$i,A:$i]:
% 0.56/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.56/0.74       ( zip_tseitin_1 @ B @ A ) ))).
% 0.56/0.74  thf('28', plain,
% 0.56/0.74      (![X33 : $i, X34 : $i]:
% 0.56/0.74         ((zip_tseitin_1 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.56/0.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.56/0.74  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('30', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_1 @ X0 @ X1))),
% 0.56/0.74      inference('sup+', [status(thm)], ['28', '29'])).
% 0.56/0.74  thf('31', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.56/0.74  thf(zf_stmt_6, axiom,
% 0.56/0.74    (![C:$i,B:$i,A:$i]:
% 0.56/0.74     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.56/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.56/0.74  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $o).
% 0.56/0.74  thf(zf_stmt_8, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.74       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.56/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.56/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.56/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.56/0.74  thf('32', plain,
% 0.56/0.74      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.56/0.74         (~ (zip_tseitin_1 @ X38 @ X39)
% 0.56/0.74          | (zip_tseitin_2 @ X40 @ X38 @ X39)
% 0.56/0.74          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.56/0.74  thf('33', plain,
% 0.56/0.74      (((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.56/0.74        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.56/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.56/0.74  thf('34', plain,
% 0.56/0.74      (((v1_xboole_0 @ sk_B) | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.56/0.74      inference('sup-', [status(thm)], ['30', '33'])).
% 0.56/0.74  thf('35', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('36', plain,
% 0.56/0.74      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.56/0.74         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.56/0.74          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 0.56/0.74          | ~ (zip_tseitin_2 @ X37 @ X36 @ X35))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.56/0.74  thf('37', plain,
% 0.56/0.74      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.56/0.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['35', '36'])).
% 0.56/0.74  thf('38', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.56/0.74  thf('39', plain,
% 0.56/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.56/0.74         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.56/0.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.56/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.56/0.74  thf('40', plain,
% 0.56/0.74      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.56/0.74      inference('sup-', [status(thm)], ['38', '39'])).
% 0.56/0.74  thf('41', plain,
% 0.56/0.74      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.56/0.74        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.56/0.74      inference('demod', [status(thm)], ['37', '40'])).
% 0.56/0.74  thf('42', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['34', '41'])).
% 0.56/0.74  thf('43', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(dt_k7_relset_1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.74       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.56/0.74  thf('44', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.56/0.74          | (m1_subset_1 @ (k7_relset_1 @ X23 @ X24 @ X22 @ X25) @ 
% 0.56/0.74             (k1_zfmisc_1 @ X24)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.56/0.74  thf('45', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.56/0.74          (k1_zfmisc_1 @ sk_B))),
% 0.56/0.74      inference('sup-', [status(thm)], ['43', '44'])).
% 0.56/0.74  thf(t5_subset, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.56/0.74          ( v1_xboole_0 @ C ) ) ))).
% 0.56/0.74  thf('46', plain,
% 0.56/0.74      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.56/0.74         (~ (r2_hidden @ X2 @ X3)
% 0.56/0.74          | ~ (v1_xboole_0 @ X4)
% 0.56/0.74          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t5_subset])).
% 0.56/0.74  thf('47', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ sk_B)
% 0.56/0.74          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['45', '46'])).
% 0.56/0.74  thf('48', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         (((sk_A) = (k1_relat_1 @ sk_D_1))
% 0.56/0.74          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['42', '47'])).
% 0.56/0.74  thf('49', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.56/0.74      inference('sup-', [status(thm)], ['27', '48'])).
% 0.56/0.74  thf('50', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.56/0.74      inference('demod', [status(thm)], ['26', '49'])).
% 0.56/0.74  thf(t1_subset, axiom,
% 0.56/0.74    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.56/0.74  thf('51', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.56/0.74      inference('cnf', [status(esa)], [t1_subset])).
% 0.56/0.74  thf('52', plain, ((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.56/0.74      inference('sup-', [status(thm)], ['50', '51'])).
% 0.56/0.74  thf('53', plain, ($false), inference('demod', [status(thm)], ['23', '52'])).
% 0.56/0.74  
% 0.56/0.74  % SZS output end Refutation
% 0.56/0.74  
% 0.56/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
