%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yZCDJV1fLw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:20 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 330 expanded)
%              Number of leaves         :   38 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :  701 (4077 expanded)
%              Number of equality atoms :   54 ( 221 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 ) ),
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
    ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ( ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_3 ) ),
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
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('25',plain,(
    ! [X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 ) @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['26','27','32'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('35',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_3 ) @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','35'])).

thf('37',plain,(
    ! [X34: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_3 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D_1 @ sk_A @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('40',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k2_relat_1 @ X10 ) )
      | ( X13
        = ( k1_funct_1 @ X10 @ ( sk_D_1 @ X13 @ X10 ) ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('41',plain,(
    ! [X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X10 ) )
      | ( X13
        = ( k1_funct_1 @ X10 @ ( sk_D_1 @ X13 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_1 @ sk_A @ sk_D_3 ) ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['30','31'])).

thf('45',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_1 @ sk_A @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','47'])).

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

thf('49',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X30 @ X31 @ X32 ) @ X31 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
        = X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t16_funct_2])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_funct_2 @ sk_D_3 @ sk_B_1 @ k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ k1_xboole_0 @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('54',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('56',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_relat_1 @ sk_D_3 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ k1_xboole_0 @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51','54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_D_3 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_D_3 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['6','62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yZCDJV1fLw
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.73  % Solved by: fo/fo7.sh
% 0.51/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.73  % done 236 iterations in 0.275s
% 0.51/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.73  % SZS output start Refutation
% 0.51/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.73  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.51/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.51/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.51/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.51/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.51/0.73  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.51/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.73  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.51/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.51/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.73  thf(t190_funct_2, conjecture,
% 0.51/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.51/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.51/0.73       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.51/0.73            ( ![E:$i]:
% 0.51/0.73              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.51/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.73        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.51/0.73            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.51/0.73          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.51/0.73               ( ![E:$i]:
% 0.51/0.73                 ( ( m1_subset_1 @ E @ B ) =>
% 0.51/0.73                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.51/0.73    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.51/0.73  thf('0', plain,
% 0.51/0.73      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(d1_xboole_0, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.73  thf('1', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.73  thf('2', plain, (~ (v1_xboole_0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3))),
% 0.51/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.51/0.73  thf('3', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.51/0.73  thf('4', plain,
% 0.51/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.73         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.51/0.73          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.51/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.51/0.73  thf('5', plain,
% 0.51/0.73      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.51/0.73  thf('6', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('demod', [status(thm)], ['2', '5'])).
% 0.51/0.73  thf('7', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(d1_funct_2, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.51/0.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.51/0.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.51/0.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.51/0.73  thf(zf_stmt_1, axiom,
% 0.51/0.73    (![B:$i,A:$i]:
% 0.51/0.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.73       ( zip_tseitin_0 @ B @ A ) ))).
% 0.51/0.73  thf('8', plain,
% 0.51/0.73      (![X22 : $i, X23 : $i]:
% 0.51/0.73         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.51/0.73  thf('9', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.51/0.73  thf(zf_stmt_3, axiom,
% 0.51/0.73    (![C:$i,B:$i,A:$i]:
% 0.51/0.73     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.51/0.73       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.51/0.73  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.51/0.73  thf(zf_stmt_5, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.73       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.51/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.51/0.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.51/0.73  thf('10', plain,
% 0.51/0.73      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.51/0.73         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.51/0.73          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.51/0.73          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.51/0.73  thf('11', plain,
% 0.51/0.73      (((zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1)
% 0.51/0.73        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.73  thf('12', plain,
% 0.51/0.73      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['8', '11'])).
% 0.51/0.73  thf('13', plain, ((v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('14', plain,
% 0.51/0.73      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.51/0.73         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.51/0.73          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.51/0.73          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.51/0.73  thf('15', plain,
% 0.51/0.73      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1)
% 0.51/0.73        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.51/0.73  thf('16', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.51/0.73  thf('17', plain,
% 0.51/0.73      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.73         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.51/0.73          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.51/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.51/0.73  thf('18', plain,
% 0.51/0.73      (((k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.73  thf('19', plain,
% 0.51/0.73      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1)
% 0.51/0.73        | ((sk_B_1) = (k1_relat_1 @ sk_D_3)))),
% 0.51/0.73      inference('demod', [status(thm)], ['15', '18'])).
% 0.51/0.73  thf('20', plain,
% 0.51/0.73      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_relat_1 @ sk_D_3)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['12', '19'])).
% 0.51/0.73  thf('21', plain,
% 0.51/0.73      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('22', plain,
% 0.51/0.73      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.51/0.73  thf('23', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('demod', [status(thm)], ['21', '22'])).
% 0.51/0.73  thf(d5_funct_1, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.73       ( ![B:$i]:
% 0.51/0.73         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.51/0.73           ( ![C:$i]:
% 0.51/0.73             ( ( r2_hidden @ C @ B ) <=>
% 0.51/0.73               ( ?[D:$i]:
% 0.51/0.73                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.51/0.73                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.51/0.73  thf('24', plain,
% 0.51/0.73      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.51/0.73         (((X12) != (k2_relat_1 @ X10))
% 0.51/0.73          | (r2_hidden @ (sk_D_1 @ X13 @ X10) @ (k1_relat_1 @ X10))
% 0.51/0.73          | ~ (r2_hidden @ X13 @ X12)
% 0.51/0.73          | ~ (v1_funct_1 @ X10)
% 0.51/0.73          | ~ (v1_relat_1 @ X10))),
% 0.51/0.73      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.51/0.73  thf('25', plain,
% 0.51/0.73      (![X10 : $i, X13 : $i]:
% 0.51/0.73         (~ (v1_relat_1 @ X10)
% 0.51/0.73          | ~ (v1_funct_1 @ X10)
% 0.51/0.73          | ~ (r2_hidden @ X13 @ (k2_relat_1 @ X10))
% 0.51/0.73          | (r2_hidden @ (sk_D_1 @ X13 @ X10) @ (k1_relat_1 @ X10)))),
% 0.51/0.73      inference('simplify', [status(thm)], ['24'])).
% 0.51/0.73  thf('26', plain,
% 0.51/0.73      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_3) @ (k1_relat_1 @ sk_D_3))
% 0.51/0.73        | ~ (v1_funct_1 @ sk_D_3)
% 0.51/0.73        | ~ (v1_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('sup-', [status(thm)], ['23', '25'])).
% 0.51/0.73  thf('27', plain, ((v1_funct_1 @ sk_D_3)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('28', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(cc2_relat_1, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( v1_relat_1 @ A ) =>
% 0.51/0.73       ( ![B:$i]:
% 0.51/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.51/0.73  thf('29', plain,
% 0.51/0.73      (![X5 : $i, X6 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.51/0.73          | (v1_relat_1 @ X5)
% 0.51/0.73          | ~ (v1_relat_1 @ X6))),
% 0.51/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.73  thf('30', plain,
% 0.51/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))
% 0.51/0.73        | (v1_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.73  thf(fc6_relat_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.51/0.73  thf('31', plain,
% 0.51/0.73      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.51/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.51/0.73  thf('32', plain, ((v1_relat_1 @ sk_D_3)),
% 0.51/0.73      inference('demod', [status(thm)], ['30', '31'])).
% 0.51/0.73  thf('33', plain,
% 0.51/0.73      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_3) @ (k1_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('demod', [status(thm)], ['26', '27', '32'])).
% 0.51/0.73  thf(t1_subset, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.51/0.73  thf('34', plain,
% 0.51/0.73      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.51/0.73      inference('cnf', [status(esa)], [t1_subset])).
% 0.51/0.73  thf('35', plain,
% 0.51/0.73      ((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_3) @ (k1_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.73  thf('36', plain,
% 0.51/0.73      (((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_3) @ sk_B_1)
% 0.51/0.73        | ((sk_C_1) = (k1_xboole_0)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['20', '35'])).
% 0.51/0.73  thf('37', plain,
% 0.51/0.73      (![X34 : $i]:
% 0.51/0.73         (((sk_A) != (k1_funct_1 @ sk_D_3 @ X34))
% 0.51/0.73          | ~ (m1_subset_1 @ X34 @ sk_B_1))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('38', plain,
% 0.51/0.73      ((((sk_C_1) = (k1_xboole_0))
% 0.51/0.73        | ((sk_A) != (k1_funct_1 @ sk_D_3 @ (sk_D_1 @ sk_A @ sk_D_3))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.73  thf('39', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('demod', [status(thm)], ['21', '22'])).
% 0.51/0.73  thf('40', plain,
% 0.51/0.73      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.51/0.73         (((X12) != (k2_relat_1 @ X10))
% 0.51/0.73          | ((X13) = (k1_funct_1 @ X10 @ (sk_D_1 @ X13 @ X10)))
% 0.51/0.73          | ~ (r2_hidden @ X13 @ X12)
% 0.51/0.73          | ~ (v1_funct_1 @ X10)
% 0.51/0.73          | ~ (v1_relat_1 @ X10))),
% 0.51/0.73      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.51/0.73  thf('41', plain,
% 0.51/0.73      (![X10 : $i, X13 : $i]:
% 0.51/0.73         (~ (v1_relat_1 @ X10)
% 0.51/0.73          | ~ (v1_funct_1 @ X10)
% 0.51/0.73          | ~ (r2_hidden @ X13 @ (k2_relat_1 @ X10))
% 0.51/0.73          | ((X13) = (k1_funct_1 @ X10 @ (sk_D_1 @ X13 @ X10))))),
% 0.51/0.73      inference('simplify', [status(thm)], ['40'])).
% 0.51/0.73  thf('42', plain,
% 0.51/0.73      ((((sk_A) = (k1_funct_1 @ sk_D_3 @ (sk_D_1 @ sk_A @ sk_D_3)))
% 0.51/0.73        | ~ (v1_funct_1 @ sk_D_3)
% 0.51/0.73        | ~ (v1_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('sup-', [status(thm)], ['39', '41'])).
% 0.51/0.73  thf('43', plain, ((v1_funct_1 @ sk_D_3)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('44', plain, ((v1_relat_1 @ sk_D_3)),
% 0.51/0.73      inference('demod', [status(thm)], ['30', '31'])).
% 0.51/0.73  thf('45', plain,
% 0.51/0.73      (((sk_A) = (k1_funct_1 @ sk_D_3 @ (sk_D_1 @ sk_A @ sk_D_3)))),
% 0.51/0.73      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.51/0.73  thf('46', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['38', '45'])).
% 0.51/0.73  thf('47', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.51/0.73      inference('simplify', [status(thm)], ['46'])).
% 0.51/0.73  thf('48', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_D_3 @ 
% 0.51/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0)))),
% 0.51/0.73      inference('demod', [status(thm)], ['7', '47'])).
% 0.51/0.73  thf(t16_funct_2, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.51/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.73       ( ( ![D:$i]:
% 0.51/0.73           ( ~( ( r2_hidden @ D @ B ) & 
% 0.51/0.73                ( ![E:$i]:
% 0.51/0.73                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.51/0.73                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.51/0.73         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.51/0.73  thf('49', plain,
% 0.51/0.73      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.51/0.73         ((r2_hidden @ (sk_D_2 @ X30 @ X31 @ X32) @ X31)
% 0.51/0.73          | ((k2_relset_1 @ X32 @ X31 @ X30) = (X31))
% 0.51/0.73          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.51/0.73          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 0.51/0.73          | ~ (v1_funct_1 @ X30))),
% 0.51/0.73      inference('cnf', [status(esa)], [t16_funct_2])).
% 0.51/0.73  thf('50', plain,
% 0.51/0.73      ((~ (v1_funct_1 @ sk_D_3)
% 0.51/0.73        | ~ (v1_funct_2 @ sk_D_3 @ sk_B_1 @ k1_xboole_0)
% 0.51/0.73        | ((k2_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3) = (k1_xboole_0))
% 0.51/0.73        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ k1_xboole_0 @ sk_B_1) @ k1_xboole_0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['48', '49'])).
% 0.51/0.73  thf('51', plain, ((v1_funct_1 @ sk_D_3)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('52', plain, ((v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('53', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.51/0.73      inference('simplify', [status(thm)], ['46'])).
% 0.51/0.73  thf('54', plain, ((v1_funct_2 @ sk_D_3 @ sk_B_1 @ k1_xboole_0)),
% 0.51/0.73      inference('demod', [status(thm)], ['52', '53'])).
% 0.51/0.73  thf('55', plain,
% 0.51/0.73      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.51/0.73  thf('56', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.51/0.73      inference('simplify', [status(thm)], ['46'])).
% 0.51/0.73  thf('57', plain,
% 0.51/0.73      (((k2_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.51/0.73      inference('demod', [status(thm)], ['55', '56'])).
% 0.51/0.73  thf('58', plain,
% 0.51/0.73      ((((k2_relat_1 @ sk_D_3) = (k1_xboole_0))
% 0.51/0.73        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ k1_xboole_0 @ sk_B_1) @ k1_xboole_0))),
% 0.51/0.73      inference('demod', [status(thm)], ['50', '51', '54', '57'])).
% 0.51/0.73  thf('59', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.73  thf('60', plain,
% 0.51/0.73      ((((k2_relat_1 @ sk_D_3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['58', '59'])).
% 0.51/0.73  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.51/0.73  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.51/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.51/0.73  thf('62', plain, (((k2_relat_1 @ sk_D_3) = (k1_xboole_0))),
% 0.51/0.73      inference('demod', [status(thm)], ['60', '61'])).
% 0.51/0.73  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.51/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.51/0.73  thf('64', plain, ($false),
% 0.51/0.73      inference('demod', [status(thm)], ['6', '62', '63'])).
% 0.51/0.73  
% 0.51/0.73  % SZS output end Refutation
% 0.51/0.73  
% 0.51/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
