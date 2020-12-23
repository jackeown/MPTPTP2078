%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.unG9q2ZC4i

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:27 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 179 expanded)
%              Number of leaves         :   38 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  620 (2148 expanded)
%              Number of equality atoms :   43 ( 107 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['16','19'])).

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

thf('21',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_D_1 @ X5 @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('22',plain,(
    ! [X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_D_1 @ X5 @ X2 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf('30',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_2 @ X33 )
       != sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) )
     != sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('33',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k2_relat_1 @ X2 ) )
      | ( X5
        = ( k1_funct_1 @ X2 @ ( sk_D_1 @ X5 @ X2 ) ) )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('34',plain,(
    ! [X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k2_relat_1 @ X2 ) )
      | ( X5
        = ( k1_funct_1 @ X2 @ ( sk_D_1 @ X5 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('38',plain,
    ( sk_C_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 != sk_C_1 ) ),
    inference(demod,[status(thm)],['31','38'])).

thf('40',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    v5_relat_1 @ sk_D_2 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['2','40'])).

thf('42',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('43',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X8 ) @ X10 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v5_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v5_relat_1 @ sk_D_2 @ X0 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('46',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( sk_C_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D_2 @ X0 )
      | ( r2_hidden @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    r2_hidden @ sk_C_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','48'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('51',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.unG9q2ZC4i
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 133 iterations in 0.256s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.50/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.50/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.50/0.71  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.50/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.50/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.50/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.50/0.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.50/0.71  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.50/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.50/0.71  thf(t17_funct_2, conjecture,
% 0.50/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.71       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.50/0.71            ( ![E:$i]:
% 0.50/0.71              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.71            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.71          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.50/0.71               ( ![E:$i]:
% 0.50/0.71                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.50/0.71                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.50/0.71  thf('0', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(cc2_relset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.50/0.71  thf('1', plain,
% 0.50/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.71         ((v5_relat_1 @ X16 @ X18)
% 0.50/0.71          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.50/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.71  thf('2', plain, ((v5_relat_1 @ sk_D_2 @ sk_B)),
% 0.50/0.71      inference('sup-', [status(thm)], ['0', '1'])).
% 0.50/0.71  thf(d1_funct_2, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.50/0.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.50/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.50/0.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.50/0.71  thf(zf_stmt_1, axiom,
% 0.50/0.71    (![B:$i,A:$i]:
% 0.50/0.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.71       ( zip_tseitin_0 @ B @ A ) ))).
% 0.50/0.71  thf('3', plain,
% 0.50/0.71      (![X25 : $i, X26 : $i]:
% 0.50/0.71         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.71  thf('4', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.50/0.71  thf(zf_stmt_3, axiom,
% 0.50/0.71    (![C:$i,B:$i,A:$i]:
% 0.50/0.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.50/0.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.50/0.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.50/0.71  thf(zf_stmt_5, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.50/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.50/0.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.50/0.71         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.50/0.71          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.50/0.71          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.50/0.71        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.50/0.71  thf('7', plain,
% 0.50/0.71      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['3', '6'])).
% 0.50/0.71  thf('8', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('9', plain,
% 0.50/0.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.50/0.71         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.50/0.71          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.50/0.71          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.71  thf('10', plain,
% 0.50/0.71      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.50/0.71        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.71  thf('11', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.50/0.71  thf('12', plain,
% 0.50/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.71         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.50/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.50/0.71  thf('13', plain,
% 0.50/0.71      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.50/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.50/0.71        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.50/0.71      inference('demod', [status(thm)], ['10', '13'])).
% 0.50/0.71  thf('15', plain,
% 0.50/0.71      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['7', '14'])).
% 0.50/0.71  thf('16', plain,
% 0.50/0.71      ((r2_hidden @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_2))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('17', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.50/0.71  thf('18', plain,
% 0.50/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.71         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.50/0.71          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.50/0.71  thf('19', plain,
% 0.50/0.71      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.50/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.50/0.71  thf('20', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.50/0.71      inference('demod', [status(thm)], ['16', '19'])).
% 0.50/0.71  thf(d5_funct_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.50/0.71           ( ![C:$i]:
% 0.50/0.71             ( ( r2_hidden @ C @ B ) <=>
% 0.50/0.71               ( ?[D:$i]:
% 0.50/0.71                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.50/0.71                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.50/0.71         (((X4) != (k2_relat_1 @ X2))
% 0.50/0.71          | (r2_hidden @ (sk_D_1 @ X5 @ X2) @ (k1_relat_1 @ X2))
% 0.50/0.71          | ~ (r2_hidden @ X5 @ X4)
% 0.50/0.71          | ~ (v1_funct_1 @ X2)
% 0.50/0.71          | ~ (v1_relat_1 @ X2))),
% 0.50/0.71      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.50/0.71  thf('22', plain,
% 0.50/0.71      (![X2 : $i, X5 : $i]:
% 0.50/0.71         (~ (v1_relat_1 @ X2)
% 0.50/0.71          | ~ (v1_funct_1 @ X2)
% 0.50/0.71          | ~ (r2_hidden @ X5 @ (k2_relat_1 @ X2))
% 0.50/0.71          | (r2_hidden @ (sk_D_1 @ X5 @ X2) @ (k1_relat_1 @ X2)))),
% 0.50/0.71      inference('simplify', [status(thm)], ['21'])).
% 0.50/0.71  thf('23', plain,
% 0.50/0.71      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.50/0.71        | ~ (v1_funct_1 @ sk_D_2)
% 0.50/0.71        | ~ (v1_relat_1 @ sk_D_2))),
% 0.50/0.71      inference('sup-', [status(thm)], ['20', '22'])).
% 0.50/0.71  thf('24', plain, ((v1_funct_1 @ sk_D_2)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('25', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(cc1_relset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( v1_relat_1 @ C ) ))).
% 0.50/0.71  thf('26', plain,
% 0.50/0.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.50/0.71         ((v1_relat_1 @ X13)
% 0.50/0.71          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.50/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.50/0.71  thf('27', plain, ((v1_relat_1 @ sk_D_2)),
% 0.50/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.50/0.71  thf('28', plain,
% 0.50/0.71      ((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.50/0.71      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.50/0.71  thf('29', plain,
% 0.50/0.71      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ sk_A)
% 0.50/0.71        | ((sk_B) = (k1_xboole_0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['15', '28'])).
% 0.50/0.71  thf('30', plain,
% 0.50/0.71      (![X33 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X33 @ sk_A)
% 0.50/0.71          | ((k1_funct_1 @ sk_D_2 @ X33) != (sk_C_1)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('31', plain,
% 0.50/0.71      ((((sk_B) = (k1_xboole_0))
% 0.50/0.71        | ((k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)) != (sk_C_1)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.71  thf('32', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.50/0.71      inference('demod', [status(thm)], ['16', '19'])).
% 0.50/0.71  thf('33', plain,
% 0.50/0.71      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.50/0.71         (((X4) != (k2_relat_1 @ X2))
% 0.50/0.71          | ((X5) = (k1_funct_1 @ X2 @ (sk_D_1 @ X5 @ X2)))
% 0.50/0.71          | ~ (r2_hidden @ X5 @ X4)
% 0.50/0.71          | ~ (v1_funct_1 @ X2)
% 0.50/0.71          | ~ (v1_relat_1 @ X2))),
% 0.50/0.71      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.50/0.71  thf('34', plain,
% 0.50/0.71      (![X2 : $i, X5 : $i]:
% 0.50/0.71         (~ (v1_relat_1 @ X2)
% 0.50/0.71          | ~ (v1_funct_1 @ X2)
% 0.50/0.71          | ~ (r2_hidden @ X5 @ (k2_relat_1 @ X2))
% 0.50/0.71          | ((X5) = (k1_funct_1 @ X2 @ (sk_D_1 @ X5 @ X2))))),
% 0.50/0.71      inference('simplify', [status(thm)], ['33'])).
% 0.50/0.71  thf('35', plain,
% 0.50/0.71      ((((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))
% 0.50/0.71        | ~ (v1_funct_1 @ sk_D_2)
% 0.50/0.71        | ~ (v1_relat_1 @ sk_D_2))),
% 0.50/0.71      inference('sup-', [status(thm)], ['32', '34'])).
% 0.50/0.71  thf('36', plain, ((v1_funct_1 @ sk_D_2)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('37', plain, ((v1_relat_1 @ sk_D_2)),
% 0.50/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.50/0.71  thf('38', plain,
% 0.50/0.71      (((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))),
% 0.50/0.71      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.50/0.71  thf('39', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_1) != (sk_C_1)))),
% 0.50/0.71      inference('demod', [status(thm)], ['31', '38'])).
% 0.50/0.71  thf('40', plain, (((sk_B) = (k1_xboole_0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['39'])).
% 0.50/0.71  thf('41', plain, ((v5_relat_1 @ sk_D_2 @ k1_xboole_0)),
% 0.50/0.71      inference('demod', [status(thm)], ['2', '40'])).
% 0.50/0.71  thf('42', plain,
% 0.50/0.71      ((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.50/0.71      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.50/0.71  thf(t172_funct_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.50/0.71       ( ![C:$i]:
% 0.50/0.71         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.50/0.71           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.50/0.71  thf('43', plain,
% 0.50/0.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.50/0.71          | (r2_hidden @ (k1_funct_1 @ X9 @ X8) @ X10)
% 0.50/0.71          | ~ (v1_funct_1 @ X9)
% 0.50/0.71          | ~ (v5_relat_1 @ X9 @ X10)
% 0.50/0.71          | ~ (v1_relat_1 @ X9))),
% 0.50/0.71      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.50/0.71  thf('44', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (v1_relat_1 @ sk_D_2)
% 0.50/0.71          | ~ (v5_relat_1 @ sk_D_2 @ X0)
% 0.50/0.71          | ~ (v1_funct_1 @ sk_D_2)
% 0.50/0.71          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)) @ 
% 0.50/0.71             X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.50/0.71  thf('45', plain, ((v1_relat_1 @ sk_D_2)),
% 0.50/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.50/0.71  thf('46', plain, ((v1_funct_1 @ sk_D_2)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('47', plain,
% 0.50/0.71      (((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))),
% 0.50/0.71      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.50/0.71  thf('48', plain,
% 0.50/0.71      (![X0 : $i]: (~ (v5_relat_1 @ sk_D_2 @ X0) | (r2_hidden @ sk_C_1 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.50/0.71  thf('49', plain, ((r2_hidden @ sk_C_1 @ k1_xboole_0)),
% 0.50/0.71      inference('sup-', [status(thm)], ['41', '48'])).
% 0.50/0.71  thf(t7_ordinal1, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.71  thf('50', plain,
% 0.50/0.71      (![X11 : $i, X12 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.50/0.71      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.50/0.71  thf('51', plain, (~ (r1_tarski @ k1_xboole_0 @ sk_C_1)),
% 0.50/0.71      inference('sup-', [status(thm)], ['49', '50'])).
% 0.50/0.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.50/0.71  thf('52', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.50/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.71  thf('53', plain, ($false), inference('demod', [status(thm)], ['51', '52'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
