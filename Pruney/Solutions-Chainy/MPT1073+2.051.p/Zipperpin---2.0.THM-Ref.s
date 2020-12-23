%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4kZN6MBnHw

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:20 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  126 (1410 expanded)
%              Number of leaves         :   38 ( 422 expanded)
%              Depth                    :   19
%              Number of atoms          :  818 (18276 expanded)
%              Number of equality atoms :   69 ( 962 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 ) @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1 ),
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

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('26',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('30',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('33',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X33: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_2 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
     != ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('38',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k2_relat_1 @ X10 ) )
      | ( X13
        = ( k1_funct_1 @ X10 @ ( sk_D_1 @ X13 @ X10 ) ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('39',plain,(
    ! [X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X10 ) )
      | ( X13
        = ( k1_funct_1 @ X10 @ ( sk_D_1 @ X13 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12'])).

thf('43',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['23','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('49',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 != k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('55',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( X18
       != ( k1_funct_1 @ X17 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ X16 @ ( k1_funct_1 @ X17 @ X16 ) ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ) @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('62',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12'])).

thf('64',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_A ) @ sk_D_2 ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','66'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('71',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['46','69','70'])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('73',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('74',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('75',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('77',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('78',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('79',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('80',plain,(
    ! [X25: $i] :
      ( zip_tseitin_0 @ X25 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['78','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['81'])).

thf('83',plain,(
    zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76','77','82'])).

thf('84',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['71','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['16','84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4kZN6MBnHw
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.74  % Solved by: fo/fo7.sh
% 0.51/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.74  % done 202 iterations in 0.289s
% 0.51/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.74  % SZS output start Refutation
% 0.51/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.74  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.51/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.51/0.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.51/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.51/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.51/0.74  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.51/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.74  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.51/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.51/0.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.74  thf(t190_funct_2, conjecture,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.51/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.51/0.74       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.51/0.74            ( ![E:$i]:
% 0.51/0.74              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.51/0.74            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.51/0.74          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.51/0.74               ( ![E:$i]:
% 0.51/0.74                 ( ( m1_subset_1 @ E @ B ) =>
% 0.51/0.74                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.51/0.74    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.51/0.74  thf('0', plain,
% 0.51/0.74      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('1', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(redefinition_k2_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.51/0.74  thf('2', plain,
% 0.51/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.51/0.74         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.51/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.51/0.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.51/0.74  thf('3', plain,
% 0.51/0.74      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.74  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.51/0.74  thf(d5_funct_1, axiom,
% 0.51/0.74    (![A:$i]:
% 0.51/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.74       ( ![B:$i]:
% 0.51/0.74         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.51/0.74           ( ![C:$i]:
% 0.51/0.74             ( ( r2_hidden @ C @ B ) <=>
% 0.51/0.74               ( ?[D:$i]:
% 0.51/0.74                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.51/0.74                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.51/0.74  thf('5', plain,
% 0.51/0.74      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.51/0.74         (((X12) != (k2_relat_1 @ X10))
% 0.51/0.74          | (r2_hidden @ (sk_D_1 @ X13 @ X10) @ (k1_relat_1 @ X10))
% 0.51/0.74          | ~ (r2_hidden @ X13 @ X12)
% 0.51/0.74          | ~ (v1_funct_1 @ X10)
% 0.51/0.74          | ~ (v1_relat_1 @ X10))),
% 0.51/0.74      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.51/0.74  thf('6', plain,
% 0.51/0.74      (![X10 : $i, X13 : $i]:
% 0.51/0.74         (~ (v1_relat_1 @ X10)
% 0.51/0.74          | ~ (v1_funct_1 @ X10)
% 0.51/0.74          | ~ (r2_hidden @ X13 @ (k2_relat_1 @ X10))
% 0.51/0.74          | (r2_hidden @ (sk_D_1 @ X13 @ X10) @ (k1_relat_1 @ X10)))),
% 0.51/0.74      inference('simplify', [status(thm)], ['5'])).
% 0.51/0.74  thf('7', plain,
% 0.51/0.74      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.51/0.74        | ~ (v1_funct_1 @ sk_D_2)
% 0.51/0.74        | ~ (v1_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('sup-', [status(thm)], ['4', '6'])).
% 0.51/0.74  thf('8', plain, ((v1_funct_1 @ sk_D_2)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('9', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(cc2_relat_1, axiom,
% 0.51/0.74    (![A:$i]:
% 0.51/0.74     ( ( v1_relat_1 @ A ) =>
% 0.51/0.74       ( ![B:$i]:
% 0.51/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.51/0.74  thf('10', plain,
% 0.51/0.74      (![X5 : $i, X6 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.51/0.74          | (v1_relat_1 @ X5)
% 0.51/0.74          | ~ (v1_relat_1 @ X6))),
% 0.51/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.74  thf('11', plain,
% 0.51/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))
% 0.51/0.74        | (v1_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.74  thf(fc6_relat_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.51/0.74  thf('12', plain,
% 0.51/0.74      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.51/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.51/0.74  thf('13', plain, ((v1_relat_1 @ sk_D_2)),
% 0.51/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.51/0.74  thf('14', plain,
% 0.51/0.74      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.51/0.74  thf(d1_xboole_0, axiom,
% 0.51/0.74    (![A:$i]:
% 0.51/0.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.74  thf('15', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.74  thf('16', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.51/0.74  thf('17', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(d1_funct_2, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.51/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.51/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.51/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_1, axiom,
% 0.51/0.74    (![C:$i,B:$i,A:$i]:
% 0.51/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.51/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.51/0.74  thf('18', plain,
% 0.51/0.74      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.51/0.74         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.51/0.74          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.51/0.74          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.51/0.74  thf('19', plain,
% 0.51/0.74      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)
% 0.51/0.74        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.51/0.74  thf('20', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.51/0.74  thf('21', plain,
% 0.51/0.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.74         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.51/0.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.51/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.51/0.74  thf('22', plain,
% 0.51/0.74      (((k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.74  thf('23', plain,
% 0.51/0.74      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)
% 0.51/0.74        | ((sk_B_1) = (k1_relat_1 @ sk_D_2)))),
% 0.51/0.74      inference('demod', [status(thm)], ['19', '22'])).
% 0.51/0.74  thf(zf_stmt_2, axiom,
% 0.51/0.74    (![B:$i,A:$i]:
% 0.51/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.74       ( zip_tseitin_0 @ B @ A ) ))).
% 0.51/0.74  thf('24', plain,
% 0.51/0.74      (![X25 : $i, X26 : $i]:
% 0.51/0.74         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.74  thf('25', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.51/0.74  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.51/0.74  thf(zf_stmt_5, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.51/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.51/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.51/0.74  thf('26', plain,
% 0.51/0.74      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.51/0.74         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.51/0.74          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.51/0.74          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.51/0.74  thf('27', plain,
% 0.51/0.74      (((zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)
% 0.51/0.74        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.74  thf('28', plain,
% 0.51/0.74      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['24', '27'])).
% 0.51/0.74  thf('29', plain,
% 0.51/0.74      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)
% 0.51/0.74        | ((sk_B_1) = (k1_relat_1 @ sk_D_2)))),
% 0.51/0.74      inference('demod', [status(thm)], ['19', '22'])).
% 0.51/0.74  thf('30', plain,
% 0.51/0.74      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_relat_1 @ sk_D_2)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.74  thf('31', plain,
% 0.51/0.74      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.51/0.74  thf(t1_subset, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.51/0.74  thf('32', plain,
% 0.51/0.74      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.51/0.74      inference('cnf', [status(esa)], [t1_subset])).
% 0.51/0.74  thf('33', plain,
% 0.51/0.74      ((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.51/0.74  thf('34', plain,
% 0.51/0.74      (((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B_1)
% 0.51/0.74        | ((sk_C_1) = (k1_xboole_0)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['30', '33'])).
% 0.51/0.74  thf('35', plain,
% 0.51/0.74      (![X33 : $i]:
% 0.51/0.74         (((sk_A) != (k1_funct_1 @ sk_D_2 @ X33))
% 0.51/0.74          | ~ (m1_subset_1 @ X33 @ sk_B_1))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('36', plain,
% 0.51/0.74      ((((sk_C_1) = (k1_xboole_0))
% 0.51/0.74        | ((sk_A) != (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['34', '35'])).
% 0.51/0.74  thf('37', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.51/0.74  thf('38', plain,
% 0.51/0.74      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.51/0.74         (((X12) != (k2_relat_1 @ X10))
% 0.51/0.74          | ((X13) = (k1_funct_1 @ X10 @ (sk_D_1 @ X13 @ X10)))
% 0.51/0.74          | ~ (r2_hidden @ X13 @ X12)
% 0.51/0.74          | ~ (v1_funct_1 @ X10)
% 0.51/0.74          | ~ (v1_relat_1 @ X10))),
% 0.51/0.74      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.51/0.74  thf('39', plain,
% 0.51/0.74      (![X10 : $i, X13 : $i]:
% 0.51/0.74         (~ (v1_relat_1 @ X10)
% 0.51/0.74          | ~ (v1_funct_1 @ X10)
% 0.51/0.74          | ~ (r2_hidden @ X13 @ (k2_relat_1 @ X10))
% 0.51/0.74          | ((X13) = (k1_funct_1 @ X10 @ (sk_D_1 @ X13 @ X10))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['38'])).
% 0.51/0.74  thf('40', plain,
% 0.51/0.74      ((((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))
% 0.51/0.74        | ~ (v1_funct_1 @ sk_D_2)
% 0.51/0.74        | ~ (v1_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('sup-', [status(thm)], ['37', '39'])).
% 0.51/0.74  thf('41', plain, ((v1_funct_1 @ sk_D_2)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('42', plain, ((v1_relat_1 @ sk_D_2)),
% 0.51/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.51/0.74  thf('43', plain,
% 0.51/0.74      (((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.51/0.74      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.51/0.74  thf('44', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.51/0.74      inference('demod', [status(thm)], ['36', '43'])).
% 0.51/0.74  thf('45', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.51/0.74      inference('simplify', [status(thm)], ['44'])).
% 0.51/0.74  thf('46', plain,
% 0.51/0.74      ((~ (zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_B_1)
% 0.51/0.74        | ((sk_B_1) = (k1_relat_1 @ sk_D_2)))),
% 0.51/0.74      inference('demod', [status(thm)], ['23', '45'])).
% 0.51/0.74  thf('47', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('48', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.51/0.74      inference('simplify', [status(thm)], ['44'])).
% 0.51/0.74  thf('49', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D_2 @ 
% 0.51/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0)))),
% 0.51/0.74      inference('demod', [status(thm)], ['47', '48'])).
% 0.51/0.74  thf('50', plain,
% 0.51/0.74      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.51/0.74         (((X30) != (k1_xboole_0))
% 0.51/0.74          | ((X31) = (k1_xboole_0))
% 0.51/0.74          | ((X32) = (k1_xboole_0))
% 0.51/0.74          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 0.51/0.74          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.51/0.74  thf('51', plain,
% 0.51/0.74      (![X31 : $i, X32 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X32 @ 
% 0.51/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ k1_xboole_0)))
% 0.51/0.74          | ~ (v1_funct_2 @ X32 @ X31 @ k1_xboole_0)
% 0.51/0.74          | ((X32) = (k1_xboole_0))
% 0.51/0.74          | ((X31) = (k1_xboole_0)))),
% 0.51/0.74      inference('simplify', [status(thm)], ['50'])).
% 0.51/0.74  thf('52', plain,
% 0.51/0.74      ((((sk_B_1) = (k1_xboole_0))
% 0.51/0.74        | ((sk_D_2) = (k1_xboole_0))
% 0.51/0.74        | ~ (v1_funct_2 @ sk_D_2 @ sk_B_1 @ k1_xboole_0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['49', '51'])).
% 0.51/0.74  thf('53', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('54', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.51/0.74      inference('simplify', [status(thm)], ['44'])).
% 0.51/0.74  thf('55', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ k1_xboole_0)),
% 0.51/0.74      inference('demod', [status(thm)], ['53', '54'])).
% 0.51/0.74  thf('56', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 0.51/0.74      inference('demod', [status(thm)], ['52', '55'])).
% 0.51/0.74  thf('57', plain,
% 0.51/0.74      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.51/0.74  thf(t8_funct_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.51/0.74       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.51/0.74         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.51/0.74           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.51/0.74  thf('58', plain,
% 0.51/0.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.51/0.74          | ((X18) != (k1_funct_1 @ X17 @ X16))
% 0.51/0.74          | (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.51/0.74          | ~ (v1_funct_1 @ X17)
% 0.51/0.74          | ~ (v1_relat_1 @ X17))),
% 0.51/0.74      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.51/0.74  thf('59', plain,
% 0.51/0.74      (![X16 : $i, X17 : $i]:
% 0.51/0.74         (~ (v1_relat_1 @ X17)
% 0.51/0.74          | ~ (v1_funct_1 @ X17)
% 0.51/0.74          | (r2_hidden @ (k4_tarski @ X16 @ (k1_funct_1 @ X17 @ X16)) @ X17)
% 0.51/0.74          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X17)))),
% 0.51/0.74      inference('simplify', [status(thm)], ['58'])).
% 0.51/0.74  thf('60', plain,
% 0.51/0.74      (((r2_hidden @ 
% 0.51/0.74         (k4_tarski @ (sk_D_1 @ sk_A @ sk_D_2) @ 
% 0.51/0.74          (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2))) @ 
% 0.51/0.74         sk_D_2)
% 0.51/0.74        | ~ (v1_funct_1 @ sk_D_2)
% 0.51/0.74        | ~ (v1_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('sup-', [status(thm)], ['57', '59'])).
% 0.51/0.74  thf('61', plain,
% 0.51/0.74      (((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.51/0.74      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.51/0.74  thf('62', plain, ((v1_funct_1 @ sk_D_2)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('63', plain, ((v1_relat_1 @ sk_D_2)),
% 0.51/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.51/0.74  thf('64', plain,
% 0.51/0.74      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_A) @ sk_D_2)),
% 0.51/0.74      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.51/0.74  thf('65', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.74  thf('66', plain, (~ (v1_xboole_0 @ sk_D_2)),
% 0.51/0.74      inference('sup-', [status(thm)], ['64', '65'])).
% 0.51/0.74  thf('67', plain,
% 0.51/0.74      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B_1) = (k1_xboole_0)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['56', '66'])).
% 0.51/0.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.51/0.74  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.51/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.51/0.74  thf('69', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['67', '68'])).
% 0.51/0.74  thf('70', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['67', '68'])).
% 0.51/0.74  thf('71', plain,
% 0.51/0.74      ((~ (zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)
% 0.51/0.74        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_2)))),
% 0.51/0.74      inference('demod', [status(thm)], ['46', '69', '70'])).
% 0.51/0.74  thf('72', plain,
% 0.51/0.74      (((zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)
% 0.51/0.74        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.74  thf('73', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.51/0.74      inference('simplify', [status(thm)], ['44'])).
% 0.51/0.74  thf('74', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.51/0.74      inference('simplify', [status(thm)], ['44'])).
% 0.51/0.74  thf('75', plain,
% 0.51/0.74      (((zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_B_1)
% 0.51/0.74        | ~ (zip_tseitin_0 @ k1_xboole_0 @ sk_B_1))),
% 0.51/0.74      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.51/0.74  thf('76', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['67', '68'])).
% 0.51/0.74  thf('77', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['67', '68'])).
% 0.51/0.74  thf('78', plain,
% 0.51/0.74      (![X25 : $i, X26 : $i]:
% 0.51/0.74         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.74  thf('79', plain,
% 0.51/0.74      (![X25 : $i, X26 : $i]:
% 0.51/0.74         ((zip_tseitin_0 @ X25 @ X26) | ((X26) != (k1_xboole_0)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.74  thf('80', plain, (![X25 : $i]: (zip_tseitin_0 @ X25 @ k1_xboole_0)),
% 0.51/0.74      inference('simplify', [status(thm)], ['79'])).
% 0.51/0.74  thf('81', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.51/0.74      inference('sup+', [status(thm)], ['78', '80'])).
% 0.51/0.74  thf('82', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.51/0.74      inference('eq_fact', [status(thm)], ['81'])).
% 0.51/0.74  thf('83', plain, ((zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)),
% 0.51/0.74      inference('demod', [status(thm)], ['75', '76', '77', '82'])).
% 0.51/0.74  thf('84', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_2))),
% 0.51/0.74      inference('demod', [status(thm)], ['71', '83'])).
% 0.51/0.74  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.51/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.51/0.74  thf('86', plain, ($false),
% 0.51/0.74      inference('demod', [status(thm)], ['16', '84', '85'])).
% 0.51/0.74  
% 0.51/0.74  % SZS output end Refutation
% 0.51/0.74  
% 0.51/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
