%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TgI5BkQcIu

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:38 EST 2020

% Result     : Theorem 10.33s
% Output     : Refutation 10.33s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 659 expanded)
%              Number of leaves         :   39 ( 208 expanded)
%              Depth                    :   24
%              Number of atoms          : 1329 (9296 expanded)
%              Number of equality atoms :  114 ( 506 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t18_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( r2_hidden @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ),
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

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_D @ X0 ) @ X0 )
      | ( X0 = sk_D )
      | ( r2_hidden @ ( sk_C_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('26',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D )
    | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( sk_C_1 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C_1 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('32',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ sk_C_3 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_C_3 @ X0 ) @ X0 )
      | ( X0 = sk_C_3 )
      | ( r2_hidden @ ( sk_C_1 @ sk_C_3 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_3 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_3 ) ),
    inference(eq_fact,[status(thm)],['37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('40',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_3 )
    | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( sk_C_1 @ sk_C_3 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C_1 @ sk_C_3 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_3 ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf('42',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_3 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('50',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 )
      | ( X23 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('51',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['43','52'])).

thf('54',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['29','53'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('65',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('68',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D )
    | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( sk_C_1 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('72',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C_1 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('74',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('76',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_3 )
    | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( sk_C_1 @ sk_C_3 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('77',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C_1 @ sk_C_3 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_3 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('79',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_3 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('81',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['74','81'])).

thf('83',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['83','84'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('86',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ ( k1_relat_1 @ sk_C_3 ) )
      | ( sk_C_3 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('89',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('90',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ sk_A )
      | ( sk_C_3 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','90','91','92'])).

thf('94',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_3 = sk_D )
    | ( r2_hidden @ ( sk_C_2 @ sk_D @ sk_C_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('97',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_3 = sk_D )
    | ( r2_hidden @ ( sk_C_2 @ sk_D @ sk_C_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['94','97','98'])).

thf('100',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_D @ sk_C_3 ) @ sk_A )
    | ( sk_C_3 = sk_D ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X35: $i] :
      ( ( ( k1_funct_1 @ sk_C_3 @ X35 )
        = ( k1_funct_1 @ sk_D @ X35 ) )
      | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( sk_C_3 = sk_D )
    | ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) ),
    inference(condensation,[status(thm)],['102'])).

thf('104',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( ( k1_funct_1 @ X14 @ ( sk_C_2 @ X13 @ X14 ) )
       != ( k1_funct_1 @ X13 @ ( sk_C_2 @ X13 @ X14 ) ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('105',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
     != ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_3 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['88','89'])).

thf('107',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('109',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('110',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['95','96'])).

thf('112',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
     != ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_3 = sk_D ) ),
    inference(demod,[status(thm)],['105','106','107','108','109','110','111'])).

thf('113',plain,(
    sk_C_3 = sk_D ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('116',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_C_3 ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['0','113','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TgI5BkQcIu
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.33/10.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.33/10.52  % Solved by: fo/fo7.sh
% 10.33/10.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.33/10.52  % done 6392 iterations in 10.022s
% 10.33/10.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.33/10.52  % SZS output start Refutation
% 10.33/10.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.33/10.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.33/10.52  thf(sk_A_type, type, sk_A: $i).
% 10.33/10.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.33/10.52  thf(sk_B_type, type, sk_B: $i).
% 10.33/10.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 10.33/10.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 10.33/10.52  thf(sk_C_3_type, type, sk_C_3: $i).
% 10.33/10.52  thf(sk_D_type, type, sk_D: $i).
% 10.33/10.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.33/10.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.33/10.52  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 10.33/10.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.33/10.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 10.33/10.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.33/10.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.33/10.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 10.33/10.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.33/10.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 10.33/10.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 10.33/10.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.33/10.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 10.33/10.52  thf(t18_funct_2, conjecture,
% 10.33/10.52    (![A:$i,B:$i,C:$i]:
% 10.33/10.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.33/10.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.33/10.52       ( ![D:$i]:
% 10.33/10.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.33/10.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.33/10.52           ( ( ![E:$i]:
% 10.33/10.52               ( ( r2_hidden @ E @ A ) =>
% 10.33/10.52                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 10.33/10.52             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 10.33/10.52  thf(zf_stmt_0, negated_conjecture,
% 10.33/10.52    (~( ![A:$i,B:$i,C:$i]:
% 10.33/10.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.33/10.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.33/10.52          ( ![D:$i]:
% 10.33/10.52            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.33/10.52                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.33/10.52              ( ( ![E:$i]:
% 10.33/10.52                  ( ( r2_hidden @ E @ A ) =>
% 10.33/10.52                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 10.33/10.52                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 10.33/10.52    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 10.33/10.52  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D)),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf(d1_funct_2, axiom,
% 10.33/10.52    (![A:$i,B:$i,C:$i]:
% 10.33/10.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.33/10.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.33/10.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 10.33/10.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 10.33/10.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.33/10.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 10.33/10.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 10.33/10.52  thf(zf_stmt_1, axiom,
% 10.33/10.52    (![B:$i,A:$i]:
% 10.33/10.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.33/10.52       ( zip_tseitin_0 @ B @ A ) ))).
% 10.33/10.52  thf('1', plain,
% 10.33/10.52      (![X27 : $i, X28 : $i]:
% 10.33/10.52         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.33/10.52  thf(t113_zfmisc_1, axiom,
% 10.33/10.52    (![A:$i,B:$i]:
% 10.33/10.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 10.33/10.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 10.33/10.52  thf('2', plain,
% 10.33/10.52      (![X8 : $i, X9 : $i]:
% 10.33/10.52         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 10.33/10.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 10.33/10.52  thf('3', plain,
% 10.33/10.52      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 10.33/10.52      inference('simplify', [status(thm)], ['2'])).
% 10.33/10.52  thf('4', plain,
% 10.33/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.52         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 10.33/10.52      inference('sup+', [status(thm)], ['1', '3'])).
% 10.33/10.52  thf('5', plain,
% 10.33/10.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 10.33/10.52  thf(zf_stmt_3, axiom,
% 10.33/10.52    (![C:$i,B:$i,A:$i]:
% 10.33/10.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 10.33/10.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 10.33/10.52  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 10.33/10.52  thf(zf_stmt_5, axiom,
% 10.33/10.52    (![A:$i,B:$i,C:$i]:
% 10.33/10.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.33/10.52       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 10.33/10.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.33/10.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 10.33/10.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 10.33/10.52  thf('6', plain,
% 10.33/10.52      (![X32 : $i, X33 : $i, X34 : $i]:
% 10.33/10.52         (~ (zip_tseitin_0 @ X32 @ X33)
% 10.33/10.52          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 10.33/10.52          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.33/10.52  thf('7', plain,
% 10.33/10.52      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.33/10.52      inference('sup-', [status(thm)], ['5', '6'])).
% 10.33/10.52  thf('8', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 10.33/10.52          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 10.33/10.52      inference('sup-', [status(thm)], ['4', '7'])).
% 10.33/10.52  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('10', plain,
% 10.33/10.52      (![X29 : $i, X30 : $i, X31 : $i]:
% 10.33/10.52         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 10.33/10.52          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 10.33/10.52          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.33/10.52  thf('11', plain,
% 10.33/10.52      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 10.33/10.52        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['9', '10'])).
% 10.33/10.52  thf('12', plain,
% 10.33/10.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf(redefinition_k1_relset_1, axiom,
% 10.33/10.52    (![A:$i,B:$i,C:$i]:
% 10.33/10.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.33/10.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 10.33/10.52  thf('13', plain,
% 10.33/10.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 10.33/10.52         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 10.33/10.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 10.33/10.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.33/10.52  thf('14', plain,
% 10.33/10.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 10.33/10.52      inference('sup-', [status(thm)], ['12', '13'])).
% 10.33/10.52  thf('15', plain,
% 10.33/10.52      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.33/10.52      inference('demod', [status(thm)], ['11', '14'])).
% 10.33/10.52  thf('16', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 10.33/10.52          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['8', '15'])).
% 10.33/10.52  thf(t2_tarski, axiom,
% 10.33/10.52    (![A:$i,B:$i]:
% 10.33/10.52     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 10.33/10.52       ( ( A ) = ( B ) ) ))).
% 10.33/10.52  thf('17', plain,
% 10.33/10.52      (![X4 : $i, X5 : $i]:
% 10.33/10.52         (((X5) = (X4))
% 10.33/10.52          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 10.33/10.52          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 10.33/10.52      inference('cnf', [status(esa)], [t2_tarski])).
% 10.33/10.52  thf('18', plain,
% 10.33/10.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf(t3_subset, axiom,
% 10.33/10.52    (![A:$i,B:$i]:
% 10.33/10.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.33/10.52  thf('19', plain,
% 10.33/10.52      (![X10 : $i, X11 : $i]:
% 10.33/10.52         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 10.33/10.52      inference('cnf', [status(esa)], [t3_subset])).
% 10.33/10.52  thf('20', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 10.33/10.52      inference('sup-', [status(thm)], ['18', '19'])).
% 10.33/10.52  thf(d3_tarski, axiom,
% 10.33/10.52    (![A:$i,B:$i]:
% 10.33/10.52     ( ( r1_tarski @ A @ B ) <=>
% 10.33/10.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 10.33/10.52  thf('21', plain,
% 10.33/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.52         (~ (r2_hidden @ X0 @ X1)
% 10.33/10.52          | (r2_hidden @ X0 @ X2)
% 10.33/10.52          | ~ (r1_tarski @ X1 @ X2))),
% 10.33/10.52      inference('cnf', [status(esa)], [d3_tarski])).
% 10.33/10.52  thf('22', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 10.33/10.52          | ~ (r2_hidden @ X0 @ sk_D))),
% 10.33/10.52      inference('sup-', [status(thm)], ['20', '21'])).
% 10.33/10.52  thf('23', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         ((r2_hidden @ (sk_C_1 @ sk_D @ X0) @ X0)
% 10.33/10.52          | ((X0) = (sk_D))
% 10.33/10.52          | (r2_hidden @ (sk_C_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['17', '22'])).
% 10.33/10.52  thf('24', plain,
% 10.33/10.52      (((r2_hidden @ (sk_C_1 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 10.33/10.52         (k2_zfmisc_1 @ sk_A @ sk_B))
% 10.33/10.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 10.33/10.52      inference('eq_fact', [status(thm)], ['23'])).
% 10.33/10.52  thf(t7_ordinal1, axiom,
% 10.33/10.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.33/10.52  thf('25', plain,
% 10.33/10.52      (![X15 : $i, X16 : $i]:
% 10.33/10.52         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 10.33/10.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 10.33/10.52  thf('26', plain,
% 10.33/10.52      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D))
% 10.33/10.52        | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 10.33/10.52             (sk_C_1 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 10.33/10.52      inference('sup-', [status(thm)], ['24', '25'])).
% 10.33/10.52  thf('27', plain,
% 10.33/10.52      ((~ (r1_tarski @ k1_xboole_0 @ 
% 10.33/10.52           (sk_C_1 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 10.33/10.52        | ((sk_A) = (k1_relat_1 @ sk_D))
% 10.33/10.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['16', '26'])).
% 10.33/10.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 10.33/10.52  thf('28', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 10.33/10.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.33/10.52  thf('29', plain,
% 10.33/10.52      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 10.33/10.52      inference('demod', [status(thm)], ['27', '28'])).
% 10.33/10.52  thf('30', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 10.33/10.52          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['8', '15'])).
% 10.33/10.52  thf('31', plain,
% 10.33/10.52      (![X4 : $i, X5 : $i]:
% 10.33/10.52         (((X5) = (X4))
% 10.33/10.52          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 10.33/10.52          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 10.33/10.52      inference('cnf', [status(esa)], [t2_tarski])).
% 10.33/10.52  thf('32', plain,
% 10.33/10.52      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('33', plain,
% 10.33/10.52      (![X10 : $i, X11 : $i]:
% 10.33/10.52         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 10.33/10.52      inference('cnf', [status(esa)], [t3_subset])).
% 10.33/10.52  thf('34', plain, ((r1_tarski @ sk_C_3 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 10.33/10.52      inference('sup-', [status(thm)], ['32', '33'])).
% 10.33/10.52  thf('35', plain,
% 10.33/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.52         (~ (r2_hidden @ X0 @ X1)
% 10.33/10.52          | (r2_hidden @ X0 @ X2)
% 10.33/10.52          | ~ (r1_tarski @ X1 @ X2))),
% 10.33/10.52      inference('cnf', [status(esa)], [d3_tarski])).
% 10.33/10.52  thf('36', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 10.33/10.52          | ~ (r2_hidden @ X0 @ sk_C_3))),
% 10.33/10.52      inference('sup-', [status(thm)], ['34', '35'])).
% 10.33/10.52  thf('37', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         ((r2_hidden @ (sk_C_1 @ sk_C_3 @ X0) @ X0)
% 10.33/10.52          | ((X0) = (sk_C_3))
% 10.33/10.52          | (r2_hidden @ (sk_C_1 @ sk_C_3 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['31', '36'])).
% 10.33/10.52  thf('38', plain,
% 10.33/10.52      (((r2_hidden @ (sk_C_1 @ sk_C_3 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 10.33/10.52         (k2_zfmisc_1 @ sk_A @ sk_B))
% 10.33/10.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_3)))),
% 10.33/10.52      inference('eq_fact', [status(thm)], ['37'])).
% 10.33/10.52  thf('39', plain,
% 10.33/10.52      (![X15 : $i, X16 : $i]:
% 10.33/10.52         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 10.33/10.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 10.33/10.52  thf('40', plain,
% 10.33/10.52      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_3))
% 10.33/10.52        | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 10.33/10.52             (sk_C_1 @ sk_C_3 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 10.33/10.52      inference('sup-', [status(thm)], ['38', '39'])).
% 10.33/10.52  thf('41', plain,
% 10.33/10.52      ((~ (r1_tarski @ k1_xboole_0 @ 
% 10.33/10.52           (sk_C_1 @ sk_C_3 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 10.33/10.52        | ((sk_A) = (k1_relat_1 @ sk_D))
% 10.33/10.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_3)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['30', '40'])).
% 10.33/10.52  thf('42', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 10.33/10.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.33/10.52  thf('43', plain,
% 10.33/10.52      ((((sk_A) = (k1_relat_1 @ sk_D))
% 10.33/10.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_3)))),
% 10.33/10.52      inference('demod', [status(thm)], ['41', '42'])).
% 10.33/10.52  thf('44', plain,
% 10.33/10.52      (![X1 : $i, X3 : $i]:
% 10.33/10.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 10.33/10.52      inference('cnf', [status(esa)], [d3_tarski])).
% 10.33/10.52  thf('45', plain,
% 10.33/10.52      (![X1 : $i, X3 : $i]:
% 10.33/10.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 10.33/10.52      inference('cnf', [status(esa)], [d3_tarski])).
% 10.33/10.52  thf('46', plain,
% 10.33/10.52      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 10.33/10.52      inference('sup-', [status(thm)], ['44', '45'])).
% 10.33/10.52  thf('47', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 10.33/10.52      inference('simplify', [status(thm)], ['46'])).
% 10.33/10.52  thf('48', plain,
% 10.33/10.52      (![X10 : $i, X12 : $i]:
% 10.33/10.52         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 10.33/10.52      inference('cnf', [status(esa)], [t3_subset])).
% 10.33/10.52  thf('49', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 10.33/10.52      inference('sup-', [status(thm)], ['47', '48'])).
% 10.33/10.52  thf(redefinition_r2_relset_1, axiom,
% 10.33/10.52    (![A:$i,B:$i,C:$i,D:$i]:
% 10.33/10.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.33/10.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.33/10.52       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 10.33/10.52  thf('50', plain,
% 10.33/10.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 10.33/10.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 10.33/10.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 10.33/10.52          | (r2_relset_1 @ X24 @ X25 @ X23 @ X26)
% 10.33/10.52          | ((X23) != (X26)))),
% 10.33/10.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.33/10.52  thf('51', plain,
% 10.33/10.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 10.33/10.52         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 10.33/10.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 10.33/10.52      inference('simplify', [status(thm)], ['50'])).
% 10.33/10.52  thf('52', plain,
% 10.33/10.52      (![X0 : $i, X1 : $i]:
% 10.33/10.52         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 10.33/10.52          (k2_zfmisc_1 @ X1 @ X0))),
% 10.33/10.52      inference('sup-', [status(thm)], ['49', '51'])).
% 10.33/10.52  thf('53', plain,
% 10.33/10.52      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 10.33/10.52        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.33/10.52      inference('sup+', [status(thm)], ['43', '52'])).
% 10.33/10.52  thf('54', plain,
% 10.33/10.52      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D)
% 10.33/10.52        | ((sk_A) = (k1_relat_1 @ sk_D))
% 10.33/10.52        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.33/10.52      inference('sup+', [status(thm)], ['29', '53'])).
% 10.33/10.52  thf('55', plain,
% 10.33/10.52      ((((sk_A) = (k1_relat_1 @ sk_D))
% 10.33/10.52        | (r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D))),
% 10.33/10.52      inference('simplify', [status(thm)], ['54'])).
% 10.33/10.52  thf('56', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D)),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('57', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 10.33/10.52      inference('clc', [status(thm)], ['55', '56'])).
% 10.33/10.52  thf('58', plain,
% 10.33/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.52         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 10.33/10.52      inference('sup+', [status(thm)], ['1', '3'])).
% 10.33/10.52  thf('59', plain,
% 10.33/10.52      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('60', plain,
% 10.33/10.52      (![X32 : $i, X33 : $i, X34 : $i]:
% 10.33/10.52         (~ (zip_tseitin_0 @ X32 @ X33)
% 10.33/10.52          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 10.33/10.52          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.33/10.52  thf('61', plain,
% 10.33/10.52      (((zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A)
% 10.33/10.52        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.33/10.52      inference('sup-', [status(thm)], ['59', '60'])).
% 10.33/10.52  thf('62', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 10.33/10.52          | (zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A))),
% 10.33/10.52      inference('sup-', [status(thm)], ['58', '61'])).
% 10.33/10.52  thf('63', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B)),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('64', plain,
% 10.33/10.52      (![X29 : $i, X30 : $i, X31 : $i]:
% 10.33/10.52         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 10.33/10.52          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 10.33/10.52          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.33/10.52  thf('65', plain,
% 10.33/10.52      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A)
% 10.33/10.52        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_3)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['63', '64'])).
% 10.33/10.52  thf('66', plain,
% 10.33/10.52      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('67', plain,
% 10.33/10.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 10.33/10.52         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 10.33/10.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 10.33/10.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.33/10.52  thf('68', plain,
% 10.33/10.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 10.33/10.52      inference('sup-', [status(thm)], ['66', '67'])).
% 10.33/10.52  thf('69', plain,
% 10.33/10.52      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A)
% 10.33/10.52        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 10.33/10.52      inference('demod', [status(thm)], ['65', '68'])).
% 10.33/10.52  thf('70', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 10.33/10.52          | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['62', '69'])).
% 10.33/10.52  thf('71', plain,
% 10.33/10.52      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D))
% 10.33/10.52        | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 10.33/10.52             (sk_C_1 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 10.33/10.52      inference('sup-', [status(thm)], ['24', '25'])).
% 10.33/10.52  thf('72', plain,
% 10.33/10.52      ((~ (r1_tarski @ k1_xboole_0 @ 
% 10.33/10.52           (sk_C_1 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 10.33/10.52        | ((sk_A) = (k1_relat_1 @ sk_C_3))
% 10.33/10.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['70', '71'])).
% 10.33/10.52  thf('73', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 10.33/10.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.33/10.52  thf('74', plain,
% 10.33/10.52      ((((sk_A) = (k1_relat_1 @ sk_C_3))
% 10.33/10.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 10.33/10.52      inference('demod', [status(thm)], ['72', '73'])).
% 10.33/10.52  thf('75', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 10.33/10.52          | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['62', '69'])).
% 10.33/10.52  thf('76', plain,
% 10.33/10.52      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_3))
% 10.33/10.52        | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 10.33/10.52             (sk_C_1 @ sk_C_3 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 10.33/10.52      inference('sup-', [status(thm)], ['38', '39'])).
% 10.33/10.52  thf('77', plain,
% 10.33/10.52      ((~ (r1_tarski @ k1_xboole_0 @ 
% 10.33/10.52           (sk_C_1 @ sk_C_3 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 10.33/10.52        | ((sk_A) = (k1_relat_1 @ sk_C_3))
% 10.33/10.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_3)))),
% 10.33/10.52      inference('sup-', [status(thm)], ['75', '76'])).
% 10.33/10.52  thf('78', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 10.33/10.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.33/10.52  thf('79', plain,
% 10.33/10.52      ((((sk_A) = (k1_relat_1 @ sk_C_3))
% 10.33/10.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_3)))),
% 10.33/10.52      inference('demod', [status(thm)], ['77', '78'])).
% 10.33/10.52  thf('80', plain,
% 10.33/10.52      (![X0 : $i, X1 : $i]:
% 10.33/10.52         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 10.33/10.52          (k2_zfmisc_1 @ X1 @ X0))),
% 10.33/10.52      inference('sup-', [status(thm)], ['49', '51'])).
% 10.33/10.52  thf('81', plain,
% 10.33/10.52      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 10.33/10.52        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 10.33/10.52      inference('sup+', [status(thm)], ['79', '80'])).
% 10.33/10.52  thf('82', plain,
% 10.33/10.52      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D)
% 10.33/10.52        | ((sk_A) = (k1_relat_1 @ sk_C_3))
% 10.33/10.52        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 10.33/10.52      inference('sup+', [status(thm)], ['74', '81'])).
% 10.33/10.52  thf('83', plain,
% 10.33/10.52      ((((sk_A) = (k1_relat_1 @ sk_C_3))
% 10.33/10.52        | (r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D))),
% 10.33/10.52      inference('simplify', [status(thm)], ['82'])).
% 10.33/10.52  thf('84', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_D)),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('85', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 10.33/10.52      inference('clc', [status(thm)], ['83', '84'])).
% 10.33/10.52  thf(t9_funct_1, axiom,
% 10.33/10.52    (![A:$i]:
% 10.33/10.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.33/10.52       ( ![B:$i]:
% 10.33/10.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 10.33/10.52           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 10.33/10.52               ( ![C:$i]:
% 10.33/10.52                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 10.33/10.52                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 10.33/10.52             ( ( A ) = ( B ) ) ) ) ) ))).
% 10.33/10.52  thf('86', plain,
% 10.33/10.52      (![X13 : $i, X14 : $i]:
% 10.33/10.52         (~ (v1_relat_1 @ X13)
% 10.33/10.52          | ~ (v1_funct_1 @ X13)
% 10.33/10.52          | ((X14) = (X13))
% 10.33/10.52          | (r2_hidden @ (sk_C_2 @ X13 @ X14) @ (k1_relat_1 @ X14))
% 10.33/10.52          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 10.33/10.52          | ~ (v1_funct_1 @ X14)
% 10.33/10.52          | ~ (v1_relat_1 @ X14))),
% 10.33/10.52      inference('cnf', [status(esa)], [t9_funct_1])).
% 10.33/10.52  thf('87', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         (((sk_A) != (k1_relat_1 @ X0))
% 10.33/10.52          | ~ (v1_relat_1 @ sk_C_3)
% 10.33/10.52          | ~ (v1_funct_1 @ sk_C_3)
% 10.33/10.52          | (r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ (k1_relat_1 @ sk_C_3))
% 10.33/10.52          | ((sk_C_3) = (X0))
% 10.33/10.52          | ~ (v1_funct_1 @ X0)
% 10.33/10.52          | ~ (v1_relat_1 @ X0))),
% 10.33/10.52      inference('sup-', [status(thm)], ['85', '86'])).
% 10.33/10.52  thf('88', plain,
% 10.33/10.52      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf(cc1_relset_1, axiom,
% 10.33/10.52    (![A:$i,B:$i,C:$i]:
% 10.33/10.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.33/10.52       ( v1_relat_1 @ C ) ))).
% 10.33/10.52  thf('89', plain,
% 10.33/10.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 10.33/10.52         ((v1_relat_1 @ X17)
% 10.33/10.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 10.33/10.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.33/10.52  thf('90', plain, ((v1_relat_1 @ sk_C_3)),
% 10.33/10.52      inference('sup-', [status(thm)], ['88', '89'])).
% 10.33/10.52  thf('91', plain, ((v1_funct_1 @ sk_C_3)),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('92', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 10.33/10.52      inference('clc', [status(thm)], ['83', '84'])).
% 10.33/10.52  thf('93', plain,
% 10.33/10.52      (![X0 : $i]:
% 10.33/10.52         (((sk_A) != (k1_relat_1 @ X0))
% 10.33/10.52          | (r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ sk_A)
% 10.33/10.52          | ((sk_C_3) = (X0))
% 10.33/10.52          | ~ (v1_funct_1 @ X0)
% 10.33/10.52          | ~ (v1_relat_1 @ X0))),
% 10.33/10.52      inference('demod', [status(thm)], ['87', '90', '91', '92'])).
% 10.33/10.52  thf('94', plain,
% 10.33/10.52      ((((sk_A) != (sk_A))
% 10.33/10.52        | ~ (v1_relat_1 @ sk_D)
% 10.33/10.52        | ~ (v1_funct_1 @ sk_D)
% 10.33/10.52        | ((sk_C_3) = (sk_D))
% 10.33/10.52        | (r2_hidden @ (sk_C_2 @ sk_D @ sk_C_3) @ sk_A))),
% 10.33/10.52      inference('sup-', [status(thm)], ['57', '93'])).
% 10.33/10.52  thf('95', plain,
% 10.33/10.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('96', plain,
% 10.33/10.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 10.33/10.52         ((v1_relat_1 @ X17)
% 10.33/10.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 10.33/10.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.33/10.52  thf('97', plain, ((v1_relat_1 @ sk_D)),
% 10.33/10.52      inference('sup-', [status(thm)], ['95', '96'])).
% 10.33/10.52  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('99', plain,
% 10.33/10.52      ((((sk_A) != (sk_A))
% 10.33/10.52        | ((sk_C_3) = (sk_D))
% 10.33/10.52        | (r2_hidden @ (sk_C_2 @ sk_D @ sk_C_3) @ sk_A))),
% 10.33/10.52      inference('demod', [status(thm)], ['94', '97', '98'])).
% 10.33/10.52  thf('100', plain,
% 10.33/10.52      (((r2_hidden @ (sk_C_2 @ sk_D @ sk_C_3) @ sk_A) | ((sk_C_3) = (sk_D)))),
% 10.33/10.52      inference('simplify', [status(thm)], ['99'])).
% 10.33/10.52  thf('101', plain,
% 10.33/10.52      (![X35 : $i]:
% 10.33/10.52         (((k1_funct_1 @ sk_C_3 @ X35) = (k1_funct_1 @ sk_D @ X35))
% 10.33/10.52          | ~ (r2_hidden @ X35 @ sk_A))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('102', plain,
% 10.33/10.52      ((((sk_C_3) = (sk_D))
% 10.33/10.52        | ((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 10.33/10.52            = (k1_funct_1 @ sk_D @ (sk_C_2 @ sk_D @ sk_C_3))))),
% 10.33/10.52      inference('sup-', [status(thm)], ['100', '101'])).
% 10.33/10.52  thf('103', plain,
% 10.33/10.52      (((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 10.33/10.52         = (k1_funct_1 @ sk_D @ (sk_C_2 @ sk_D @ sk_C_3)))),
% 10.33/10.52      inference('condensation', [status(thm)], ['102'])).
% 10.33/10.52  thf('104', plain,
% 10.33/10.52      (![X13 : $i, X14 : $i]:
% 10.33/10.52         (~ (v1_relat_1 @ X13)
% 10.33/10.52          | ~ (v1_funct_1 @ X13)
% 10.33/10.52          | ((X14) = (X13))
% 10.33/10.52          | ((k1_funct_1 @ X14 @ (sk_C_2 @ X13 @ X14))
% 10.33/10.52              != (k1_funct_1 @ X13 @ (sk_C_2 @ X13 @ X14)))
% 10.33/10.52          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 10.33/10.52          | ~ (v1_funct_1 @ X14)
% 10.33/10.52          | ~ (v1_relat_1 @ X14))),
% 10.33/10.52      inference('cnf', [status(esa)], [t9_funct_1])).
% 10.33/10.52  thf('105', plain,
% 10.33/10.52      ((((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 10.33/10.52          != (k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3)))
% 10.33/10.52        | ~ (v1_relat_1 @ sk_C_3)
% 10.33/10.52        | ~ (v1_funct_1 @ sk_C_3)
% 10.33/10.52        | ((k1_relat_1 @ sk_C_3) != (k1_relat_1 @ sk_D))
% 10.33/10.52        | ((sk_C_3) = (sk_D))
% 10.33/10.52        | ~ (v1_funct_1 @ sk_D)
% 10.33/10.52        | ~ (v1_relat_1 @ sk_D))),
% 10.33/10.52      inference('sup-', [status(thm)], ['103', '104'])).
% 10.33/10.52  thf('106', plain, ((v1_relat_1 @ sk_C_3)),
% 10.33/10.52      inference('sup-', [status(thm)], ['88', '89'])).
% 10.33/10.52  thf('107', plain, ((v1_funct_1 @ sk_C_3)),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('108', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 10.33/10.52      inference('clc', [status(thm)], ['83', '84'])).
% 10.33/10.52  thf('109', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 10.33/10.52      inference('clc', [status(thm)], ['55', '56'])).
% 10.33/10.52  thf('110', plain, ((v1_funct_1 @ sk_D)),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 10.33/10.52      inference('sup-', [status(thm)], ['95', '96'])).
% 10.33/10.52  thf('112', plain,
% 10.33/10.52      ((((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 10.33/10.52          != (k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3)))
% 10.33/10.52        | ((sk_A) != (sk_A))
% 10.33/10.52        | ((sk_C_3) = (sk_D)))),
% 10.33/10.52      inference('demod', [status(thm)],
% 10.33/10.52                ['105', '106', '107', '108', '109', '110', '111'])).
% 10.33/10.52  thf('113', plain, (((sk_C_3) = (sk_D))),
% 10.33/10.52      inference('simplify', [status(thm)], ['112'])).
% 10.33/10.52  thf('114', plain,
% 10.33/10.52      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.33/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.33/10.52  thf('115', plain,
% 10.33/10.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 10.33/10.52         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 10.33/10.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 10.33/10.52      inference('simplify', [status(thm)], ['50'])).
% 10.33/10.52  thf('116', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_3 @ sk_C_3)),
% 10.33/10.52      inference('sup-', [status(thm)], ['114', '115'])).
% 10.33/10.52  thf('117', plain, ($false),
% 10.33/10.52      inference('demod', [status(thm)], ['0', '113', '116'])).
% 10.33/10.52  
% 10.33/10.52  % SZS output end Refutation
% 10.33/10.52  
% 10.33/10.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
