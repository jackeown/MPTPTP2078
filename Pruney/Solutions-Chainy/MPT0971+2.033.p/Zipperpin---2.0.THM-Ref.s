%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VtXg26yFLK

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:31 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 321 expanded)
%              Number of leaves         :   37 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  683 (4023 expanded)
%              Number of equality atoms :   54 ( 221 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('23',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['21','22'])).

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

thf('24',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('25',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['26','27','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_3 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X32: $i] :
      ( ~ ( r2_hidden @ X32 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_3 @ X32 )
       != sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_3 @ ( sk_D_1 @ sk_C_1 @ sk_D_3 ) )
     != sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('38',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('39',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_1 @ sk_C_1 @ sk_D_3 ) ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['30','31'])).

thf('43',plain,
    ( sk_C_1
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_1 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 != sk_C_1 ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','45'])).

thf(t16_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf('47',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X28 @ X29 @ X30 ) @ X29 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
        = X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t16_funct_2])).

thf('48',plain,
    ( ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_3 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('52',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('54',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_relat_1 @ sk_D_3 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49','52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,
    ( ( ( k2_relat_1 @ sk_D_3 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_D_3 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['6','60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VtXg26yFLK
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:11:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.63  % Solved by: fo/fo7.sh
% 0.37/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.63  % done 219 iterations in 0.205s
% 0.37/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.63  % SZS output start Refutation
% 0.37/0.63  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.37/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.63  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.37/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.63  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.37/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.63  thf(t17_funct_2, conjecture,
% 0.37/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.63       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.37/0.63            ( ![E:$i]:
% 0.37/0.63              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.37/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.63            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.63          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.37/0.63               ( ![E:$i]:
% 0.37/0.63                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.37/0.63                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.37/0.63    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.37/0.63  thf('0', plain,
% 0.37/0.63      ((r2_hidden @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(d1_xboole_0, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.63  thf('1', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.63  thf('2', plain, (~ (v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3))),
% 0.37/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.63  thf('3', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.63  thf('4', plain,
% 0.37/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.63         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.37/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.37/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.63  thf('5', plain,
% 0.37/0.63      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.63  thf('6', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('demod', [status(thm)], ['2', '5'])).
% 0.37/0.63  thf('7', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(d1_funct_2, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.63  thf(zf_stmt_1, axiom,
% 0.37/0.63    (![B:$i,A:$i]:
% 0.37/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.63  thf('8', plain,
% 0.37/0.63      (![X20 : $i, X21 : $i]:
% 0.37/0.63         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.63  thf('9', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.63  thf(zf_stmt_3, axiom,
% 0.37/0.63    (![C:$i,B:$i,A:$i]:
% 0.37/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.63  thf(zf_stmt_5, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.63  thf('10', plain,
% 0.37/0.63      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.63         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.37/0.63          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.37/0.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.63  thf('11', plain,
% 0.37/0.63      (((zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.37/0.63        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.63  thf('12', plain,
% 0.37/0.63      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['8', '11'])).
% 0.37/0.63  thf('13', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('14', plain,
% 0.37/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.63         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.37/0.63          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.37/0.63          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.63  thf('15', plain,
% 0.37/0.63      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.37/0.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.63  thf('16', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.63  thf('17', plain,
% 0.37/0.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.63         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.37/0.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.37/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.63  thf('18', plain,
% 0.37/0.63      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.63  thf('19', plain,
% 0.37/0.63      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.37/0.63        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.37/0.63      inference('demod', [status(thm)], ['15', '18'])).
% 0.37/0.63  thf('20', plain,
% 0.37/0.63      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['12', '19'])).
% 0.37/0.63  thf('21', plain,
% 0.37/0.63      ((r2_hidden @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('22', plain,
% 0.37/0.63      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.63  thf('23', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.63  thf(d5_funct_1, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.37/0.63           ( ![C:$i]:
% 0.37/0.63             ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.63               ( ?[D:$i]:
% 0.37/0.63                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.37/0.63                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.37/0.63  thf('24', plain,
% 0.37/0.63      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.37/0.63         (((X10) != (k2_relat_1 @ X8))
% 0.37/0.63          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8))
% 0.37/0.63          | ~ (r2_hidden @ X11 @ X10)
% 0.37/0.63          | ~ (v1_funct_1 @ X8)
% 0.37/0.63          | ~ (v1_relat_1 @ X8))),
% 0.37/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.37/0.63  thf('25', plain,
% 0.37/0.63      (![X8 : $i, X11 : $i]:
% 0.37/0.63         (~ (v1_relat_1 @ X8)
% 0.37/0.63          | ~ (v1_funct_1 @ X8)
% 0.37/0.63          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.37/0.63          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.63  thf('26', plain,
% 0.37/0.63      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_3) @ (k1_relat_1 @ sk_D_3))
% 0.37/0.63        | ~ (v1_funct_1 @ sk_D_3)
% 0.37/0.63        | ~ (v1_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('sup-', [status(thm)], ['23', '25'])).
% 0.37/0.63  thf('27', plain, ((v1_funct_1 @ sk_D_3)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('28', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(cc2_relat_1, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( v1_relat_1 @ A ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.63  thf('29', plain,
% 0.37/0.63      (![X3 : $i, X4 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.37/0.63          | (v1_relat_1 @ X3)
% 0.37/0.63          | ~ (v1_relat_1 @ X4))),
% 0.37/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.63  thf('30', plain,
% 0.37/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.63  thf(fc6_relat_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.63  thf('31', plain,
% 0.37/0.63      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.37/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.63  thf('32', plain, ((v1_relat_1 @ sk_D_3)),
% 0.37/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.63  thf('33', plain,
% 0.37/0.63      ((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_3) @ (k1_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('demod', [status(thm)], ['26', '27', '32'])).
% 0.37/0.63  thf('34', plain,
% 0.37/0.63      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_3) @ sk_A)
% 0.37/0.63        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('sup+', [status(thm)], ['20', '33'])).
% 0.37/0.63  thf('35', plain,
% 0.37/0.63      (![X32 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X32 @ sk_A)
% 0.37/0.63          | ((k1_funct_1 @ sk_D_3 @ X32) != (sk_C_1)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('36', plain,
% 0.37/0.63      ((((sk_B_1) = (k1_xboole_0))
% 0.37/0.63        | ((k1_funct_1 @ sk_D_3 @ (sk_D_1 @ sk_C_1 @ sk_D_3)) != (sk_C_1)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.63  thf('37', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.63  thf('38', plain,
% 0.37/0.63      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.37/0.63         (((X10) != (k2_relat_1 @ X8))
% 0.37/0.63          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8)))
% 0.37/0.63          | ~ (r2_hidden @ X11 @ X10)
% 0.37/0.63          | ~ (v1_funct_1 @ X8)
% 0.37/0.63          | ~ (v1_relat_1 @ X8))),
% 0.37/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.37/0.63  thf('39', plain,
% 0.37/0.63      (![X8 : $i, X11 : $i]:
% 0.37/0.63         (~ (v1_relat_1 @ X8)
% 0.37/0.63          | ~ (v1_funct_1 @ X8)
% 0.37/0.63          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.37/0.63          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8))))),
% 0.37/0.63      inference('simplify', [status(thm)], ['38'])).
% 0.37/0.63  thf('40', plain,
% 0.37/0.63      ((((sk_C_1) = (k1_funct_1 @ sk_D_3 @ (sk_D_1 @ sk_C_1 @ sk_D_3)))
% 0.37/0.63        | ~ (v1_funct_1 @ sk_D_3)
% 0.37/0.63        | ~ (v1_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('sup-', [status(thm)], ['37', '39'])).
% 0.37/0.63  thf('41', plain, ((v1_funct_1 @ sk_D_3)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('42', plain, ((v1_relat_1 @ sk_D_3)),
% 0.37/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.63  thf('43', plain,
% 0.37/0.63      (((sk_C_1) = (k1_funct_1 @ sk_D_3 @ (sk_D_1 @ sk_C_1 @ sk_D_3)))),
% 0.37/0.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.37/0.63  thf('44', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C_1) != (sk_C_1)))),
% 0.37/0.63      inference('demod', [status(thm)], ['36', '43'])).
% 0.37/0.63  thf('45', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.37/0.63      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.63  thf('46', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_3 @ 
% 0.37/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.37/0.63      inference('demod', [status(thm)], ['7', '45'])).
% 0.37/0.63  thf(t16_funct_2, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.63       ( ( ![D:$i]:
% 0.37/0.63           ( ~( ( r2_hidden @ D @ B ) & 
% 0.37/0.63                ( ![E:$i]:
% 0.37/0.63                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.37/0.63                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.37/0.63         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.37/0.63  thf('47', plain,
% 0.37/0.63      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.63         ((r2_hidden @ (sk_D_2 @ X28 @ X29 @ X30) @ X29)
% 0.37/0.63          | ((k2_relset_1 @ X30 @ X29 @ X28) = (X29))
% 0.37/0.63          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.37/0.63          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.37/0.63          | ~ (v1_funct_1 @ X28))),
% 0.37/0.63      inference('cnf', [status(esa)], [t16_funct_2])).
% 0.37/0.63  thf('48', plain,
% 0.37/0.63      ((~ (v1_funct_1 @ sk_D_3)
% 0.37/0.63        | ~ (v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0)
% 0.37/0.63        | ((k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_3) = (k1_xboole_0))
% 0.37/0.63        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ k1_xboole_0 @ sk_A) @ k1_xboole_0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.63  thf('49', plain, ((v1_funct_1 @ sk_D_3)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('50', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('51', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.37/0.63      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.63  thf('52', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0)),
% 0.37/0.63      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.63  thf('53', plain,
% 0.37/0.63      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.63  thf('54', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.37/0.63      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.63  thf('55', plain,
% 0.37/0.63      (((k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.37/0.63      inference('demod', [status(thm)], ['53', '54'])).
% 0.37/0.63  thf('56', plain,
% 0.37/0.63      ((((k2_relat_1 @ sk_D_3) = (k1_xboole_0))
% 0.37/0.63        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ k1_xboole_0 @ sk_A) @ k1_xboole_0))),
% 0.37/0.63      inference('demod', [status(thm)], ['48', '49', '52', '55'])).
% 0.37/0.63  thf('57', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.63  thf('58', plain,
% 0.37/0.63      ((((k2_relat_1 @ sk_D_3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.63  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.63  thf('60', plain, (((k2_relat_1 @ sk_D_3) = (k1_xboole_0))),
% 0.37/0.63      inference('demod', [status(thm)], ['58', '59'])).
% 0.37/0.63  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.63  thf('62', plain, ($false),
% 0.37/0.63      inference('demod', [status(thm)], ['6', '60', '61'])).
% 0.37/0.63  
% 0.37/0.63  % SZS output end Refutation
% 0.37/0.63  
% 0.50/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
