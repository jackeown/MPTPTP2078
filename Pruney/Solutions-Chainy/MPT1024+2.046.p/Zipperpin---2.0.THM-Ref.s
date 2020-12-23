%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e0uh6pn2XI

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:40 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 165 expanded)
%              Number of leaves         :   41 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  674 (2054 expanded)
%              Number of equality atoms :   37 (  83 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
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
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k9_relat_1 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X17 @ X13 @ X14 ) @ X17 @ X13 @ X14 )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X17 @ X13 @ X14 ) @ X17 @ X13 @ X14 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_1 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_1 @ X36 @ X37 )
      | ( zip_tseitin_2 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('23',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_2 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('27',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','38'])).

thf('40',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['16','39'])).

thf('41',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_A )
      | ~ ( r2_hidden @ X39 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X9
        = ( k1_funct_1 @ X7 @ X8 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('45',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X10 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('48',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e0uh6pn2XI
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:01:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.48/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.66  % Solved by: fo/fo7.sh
% 0.48/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.66  % done 161 iterations in 0.195s
% 0.48/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.66  % SZS output start Refutation
% 0.48/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.48/0.66  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.48/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.48/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.48/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.48/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.66  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.48/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.48/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.66  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.48/0.66  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.48/0.66  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.48/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.66  thf(t115_funct_2, conjecture,
% 0.48/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.66       ( ![E:$i]:
% 0.48/0.66         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.48/0.66              ( ![F:$i]:
% 0.48/0.66                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.48/0.66                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.66        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.66            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.66          ( ![E:$i]:
% 0.48/0.66            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.48/0.66                 ( ![F:$i]:
% 0.48/0.66                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.48/0.66                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.48/0.66    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.48/0.66  thf('0', plain,
% 0.48/0.66      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('1', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(redefinition_k7_relset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.48/0.66  thf('2', plain,
% 0.48/0.66      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.48/0.66          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.48/0.66  thf('3', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.48/0.66           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.66  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.48/0.66      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.66  thf(d12_funct_1, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.48/0.66       ( ![B:$i,C:$i]:
% 0.48/0.66         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.48/0.66           ( ![D:$i]:
% 0.48/0.66             ( ( r2_hidden @ D @ C ) <=>
% 0.48/0.66               ( ?[E:$i]:
% 0.48/0.66                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.48/0.66                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.48/0.66  thf(zf_stmt_2, axiom,
% 0.48/0.66    (![E:$i,D:$i,B:$i,A:$i]:
% 0.48/0.66     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.48/0.66       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.48/0.66         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_3, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.48/0.66       ( ![B:$i,C:$i]:
% 0.48/0.66         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.48/0.66           ( ![D:$i]:
% 0.48/0.66             ( ( r2_hidden @ D @ C ) <=>
% 0.48/0.66               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.48/0.66  thf('5', plain,
% 0.48/0.66      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.48/0.66         (((X16) != (k9_relat_1 @ X14 @ X13))
% 0.48/0.66          | (zip_tseitin_0 @ (sk_E_1 @ X17 @ X13 @ X14) @ X17 @ X13 @ X14)
% 0.48/0.66          | ~ (r2_hidden @ X17 @ X16)
% 0.48/0.66          | ~ (v1_funct_1 @ X14)
% 0.48/0.66          | ~ (v1_relat_1 @ X14))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.66  thf('6', plain,
% 0.48/0.66      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ X14)
% 0.48/0.66          | ~ (v1_funct_1 @ X14)
% 0.48/0.66          | ~ (r2_hidden @ X17 @ (k9_relat_1 @ X14 @ X13))
% 0.48/0.66          | (zip_tseitin_0 @ (sk_E_1 @ X17 @ X13 @ X14) @ X17 @ X13 @ X14))),
% 0.48/0.66      inference('simplify', [status(thm)], ['5'])).
% 0.48/0.66  thf('7', plain,
% 0.48/0.66      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.48/0.66         sk_D_1)
% 0.48/0.66        | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.66        | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['4', '6'])).
% 0.48/0.66  thf('8', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('9', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(cc2_relat_1, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ A ) =>
% 0.48/0.66       ( ![B:$i]:
% 0.48/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.48/0.66  thf('10', plain,
% 0.48/0.66      (![X3 : $i, X4 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.48/0.66          | (v1_relat_1 @ X3)
% 0.48/0.66          | ~ (v1_relat_1 @ X4))),
% 0.48/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.66  thf('11', plain,
% 0.48/0.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.48/0.66  thf(fc6_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.48/0.66  thf('12', plain,
% 0.48/0.66      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.48/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.48/0.66  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.66      inference('demod', [status(thm)], ['11', '12'])).
% 0.48/0.66  thf('14', plain,
% 0.48/0.66      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.48/0.66        sk_D_1)),
% 0.48/0.66      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.48/0.66  thf('15', plain,
% 0.48/0.66      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.48/0.66         ((r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.48/0.66          | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.66  thf('16', plain,
% 0.48/0.66      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.48/0.66  thf('17', plain,
% 0.48/0.66      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(d1_funct_2, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.48/0.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.48/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.48/0.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_4, axiom,
% 0.48/0.66    (![B:$i,A:$i]:
% 0.48/0.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.66       ( zip_tseitin_1 @ B @ A ) ))).
% 0.48/0.66  thf('18', plain,
% 0.48/0.66      (![X31 : $i, X32 : $i]:
% 0.48/0.66         ((zip_tseitin_1 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.48/0.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.48/0.66  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.66  thf('20', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_1 @ X0 @ X1))),
% 0.48/0.66      inference('sup+', [status(thm)], ['18', '19'])).
% 0.48/0.66  thf('21', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.48/0.66  thf(zf_stmt_6, axiom,
% 0.48/0.66    (![C:$i,B:$i,A:$i]:
% 0.48/0.66     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.48/0.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $o).
% 0.48/0.66  thf(zf_stmt_8, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.48/0.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.48/0.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.48/0.66  thf('22', plain,
% 0.48/0.66      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.48/0.66         (~ (zip_tseitin_1 @ X36 @ X37)
% 0.48/0.66          | (zip_tseitin_2 @ X38 @ X36 @ X37)
% 0.48/0.66          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.48/0.66  thf('23', plain,
% 0.48/0.66      (((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.48/0.66        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.66  thf('24', plain,
% 0.48/0.66      (((v1_xboole_0 @ sk_B) | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['20', '23'])).
% 0.48/0.66  thf('25', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('26', plain,
% 0.48/0.66      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.48/0.66         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.48/0.66          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.48/0.66          | ~ (zip_tseitin_2 @ X35 @ X34 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.48/0.66  thf('27', plain,
% 0.48/0.66      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.48/0.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.66  thf('28', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(redefinition_k1_relset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.48/0.66  thf('29', plain,
% 0.48/0.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.48/0.66         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.48/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.48/0.66  thf('30', plain,
% 0.48/0.66      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.48/0.66  thf('31', plain,
% 0.48/0.66      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.48/0.66        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.48/0.66      inference('demod', [status(thm)], ['27', '30'])).
% 0.48/0.66  thf('32', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['24', '31'])).
% 0.48/0.66  thf('33', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(dt_k7_relset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.48/0.66  thf('34', plain,
% 0.48/0.66      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.48/0.66          | (m1_subset_1 @ (k7_relset_1 @ X21 @ X22 @ X20 @ X23) @ 
% 0.48/0.66             (k1_zfmisc_1 @ X22)))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.48/0.66  thf('35', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.48/0.66          (k1_zfmisc_1 @ sk_B))),
% 0.48/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.66  thf(t5_subset, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.48/0.66          ( v1_xboole_0 @ C ) ) ))).
% 0.48/0.66  thf('36', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.48/0.66          | ~ (v1_xboole_0 @ X2)
% 0.48/0.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t5_subset])).
% 0.48/0.66  thf('37', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (v1_xboole_0 @ sk_B)
% 0.48/0.66          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.48/0.66  thf('38', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((sk_A) = (k1_relat_1 @ sk_D_1))
% 0.48/0.66          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['32', '37'])).
% 0.48/0.66  thf('39', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['17', '38'])).
% 0.48/0.66  thf('40', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.48/0.66      inference('demod', [status(thm)], ['16', '39'])).
% 0.48/0.66  thf('41', plain,
% 0.48/0.66      (![X39 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X39 @ sk_A)
% 0.48/0.66          | ~ (r2_hidden @ X39 @ sk_C)
% 0.48/0.66          | ((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X39)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('42', plain,
% 0.48/0.66      ((((sk_E_2) != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))
% 0.48/0.66        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C))),
% 0.48/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.48/0.66  thf('43', plain,
% 0.48/0.66      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.48/0.66        sk_D_1)),
% 0.48/0.66      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.48/0.66  thf('44', plain,
% 0.48/0.66      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.48/0.66         (((X9) = (k1_funct_1 @ X7 @ X8))
% 0.48/0.66          | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.66  thf('45', plain,
% 0.48/0.66      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.48/0.66  thf('46', plain,
% 0.48/0.66      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.48/0.66        sk_D_1)),
% 0.48/0.66      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.48/0.66  thf('47', plain,
% 0.48/0.66      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.48/0.66         ((r2_hidden @ X8 @ X10) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.66  thf('48', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)),
% 0.48/0.66      inference('sup-', [status(thm)], ['46', '47'])).
% 0.48/0.66  thf('49', plain, (((sk_E_2) != (sk_E_2))),
% 0.48/0.66      inference('demod', [status(thm)], ['42', '45', '48'])).
% 0.48/0.66  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 0.48/0.66  
% 0.48/0.66  % SZS output end Refutation
% 0.48/0.66  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
