%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h8vCJ2yvdz

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:18 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 221 expanded)
%              Number of leaves         :   37 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  634 (2710 expanded)
%              Number of equality atoms :   45 ( 147 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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

thf('8',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('21',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['22','23','26'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('29',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X35: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_2 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
     != ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('34',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('35',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('39',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','41'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X18 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('44',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ k1_xboole_0 @ sk_D_2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('46',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_B @ k1_xboole_0 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','47'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('49',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','50'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('53',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h8vCJ2yvdz
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:15:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.69  % Solved by: fo/fo7.sh
% 0.44/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.69  % done 154 iterations in 0.227s
% 0.44/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.69  % SZS output start Refutation
% 0.44/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.69  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.44/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.69  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.44/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.44/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.69  thf(t190_funct_2, conjecture,
% 0.44/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.44/0.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.44/0.69       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.44/0.69            ( ![E:$i]:
% 0.44/0.69              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.44/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.44/0.69            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.44/0.69          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.44/0.69               ( ![E:$i]:
% 0.44/0.69                 ( ( m1_subset_1 @ E @ B ) =>
% 0.44/0.69                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.44/0.69    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.44/0.69  thf('0', plain,
% 0.44/0.69      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('1', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(redefinition_k2_relset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.44/0.69  thf('2', plain,
% 0.44/0.69      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.69         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.44/0.69          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.44/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.44/0.69  thf('3', plain,
% 0.44/0.69      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.44/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.69  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.44/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.44/0.69  thf('5', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(d1_funct_2, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.69  thf(zf_stmt_1, axiom,
% 0.44/0.69    (![B:$i,A:$i]:
% 0.44/0.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.69       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.69  thf('6', plain,
% 0.44/0.69      (![X27 : $i, X28 : $i]:
% 0.44/0.69         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.69  thf('7', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.69  thf(zf_stmt_3, axiom,
% 0.44/0.69    (![C:$i,B:$i,A:$i]:
% 0.44/0.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.69  thf(zf_stmt_5, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.69  thf('8', plain,
% 0.44/0.69      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.44/0.69         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.44/0.69          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.44/0.69          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.69  thf('9', plain,
% 0.44/0.69      (((zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B)
% 0.44/0.69        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B))),
% 0.44/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.69  thf('10', plain,
% 0.44/0.69      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B))),
% 0.44/0.69      inference('sup-', [status(thm)], ['6', '9'])).
% 0.44/0.69  thf('11', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_1)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('12', plain,
% 0.44/0.69      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.69         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.44/0.69          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.44/0.69          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.69  thf('13', plain,
% 0.44/0.69      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B)
% 0.44/0.69        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_2)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.69  thf('14', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.69  thf('15', plain,
% 0.44/0.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.69         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.44/0.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.44/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.69  thf('16', plain,
% 0.44/0.69      (((k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.44/0.69      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.69  thf('17', plain,
% 0.44/0.69      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B)
% 0.44/0.69        | ((sk_B) = (k1_relat_1 @ sk_D_2)))),
% 0.44/0.69      inference('demod', [status(thm)], ['13', '16'])).
% 0.44/0.69  thf('18', plain,
% 0.44/0.69      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B) = (k1_relat_1 @ sk_D_2)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['10', '17'])).
% 0.44/0.69  thf('19', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.44/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.44/0.69  thf(d5_funct_1, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.69       ( ![B:$i]:
% 0.44/0.69         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.44/0.69           ( ![C:$i]:
% 0.44/0.69             ( ( r2_hidden @ C @ B ) <=>
% 0.44/0.69               ( ?[D:$i]:
% 0.44/0.69                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.44/0.69                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.44/0.69  thf('20', plain,
% 0.44/0.69      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.44/0.69         (((X9) != (k2_relat_1 @ X7))
% 0.44/0.69          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7))
% 0.44/0.69          | ~ (r2_hidden @ X10 @ X9)
% 0.44/0.69          | ~ (v1_funct_1 @ X7)
% 0.44/0.69          | ~ (v1_relat_1 @ X7))),
% 0.44/0.69      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.44/0.69  thf('21', plain,
% 0.44/0.69      (![X7 : $i, X10 : $i]:
% 0.44/0.69         (~ (v1_relat_1 @ X7)
% 0.44/0.69          | ~ (v1_funct_1 @ X7)
% 0.44/0.69          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 0.44/0.69          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7)))),
% 0.44/0.69      inference('simplify', [status(thm)], ['20'])).
% 0.44/0.69  thf('22', plain,
% 0.44/0.69      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.44/0.69        | ~ (v1_funct_1 @ sk_D_2)
% 0.44/0.69        | ~ (v1_relat_1 @ sk_D_2))),
% 0.44/0.69      inference('sup-', [status(thm)], ['19', '21'])).
% 0.44/0.69  thf('23', plain, ((v1_funct_1 @ sk_D_2)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('24', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(cc1_relset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.69       ( v1_relat_1 @ C ) ))).
% 0.44/0.69  thf('25', plain,
% 0.44/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.69         ((v1_relat_1 @ X15)
% 0.44/0.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.44/0.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.69  thf('26', plain, ((v1_relat_1 @ sk_D_2)),
% 0.44/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.44/0.69  thf('27', plain,
% 0.44/0.69      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.44/0.69      inference('demod', [status(thm)], ['22', '23', '26'])).
% 0.44/0.69  thf(t1_subset, axiom,
% 0.44/0.69    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.44/0.69  thf('28', plain,
% 0.44/0.69      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.44/0.69      inference('cnf', [status(esa)], [t1_subset])).
% 0.44/0.69  thf('29', plain,
% 0.44/0.69      ((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.44/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.69  thf('30', plain,
% 0.44/0.69      (((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B)
% 0.44/0.69        | ((sk_C_1) = (k1_xboole_0)))),
% 0.44/0.69      inference('sup+', [status(thm)], ['18', '29'])).
% 0.44/0.69  thf('31', plain,
% 0.44/0.69      (![X35 : $i]:
% 0.44/0.69         (((sk_A) != (k1_funct_1 @ sk_D_2 @ X35))
% 0.44/0.69          | ~ (m1_subset_1 @ X35 @ sk_B))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('32', plain,
% 0.44/0.69      ((((sk_C_1) = (k1_xboole_0))
% 0.44/0.69        | ((sk_A) != (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.69  thf('33', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.44/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.44/0.69  thf('34', plain,
% 0.44/0.69      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.44/0.69         (((X9) != (k2_relat_1 @ X7))
% 0.44/0.69          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7)))
% 0.44/0.69          | ~ (r2_hidden @ X10 @ X9)
% 0.44/0.69          | ~ (v1_funct_1 @ X7)
% 0.44/0.69          | ~ (v1_relat_1 @ X7))),
% 0.44/0.69      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.44/0.69  thf('35', plain,
% 0.44/0.69      (![X7 : $i, X10 : $i]:
% 0.44/0.69         (~ (v1_relat_1 @ X7)
% 0.44/0.69          | ~ (v1_funct_1 @ X7)
% 0.44/0.69          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 0.44/0.69          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7))))),
% 0.44/0.69      inference('simplify', [status(thm)], ['34'])).
% 0.44/0.69  thf('36', plain,
% 0.44/0.69      ((((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))
% 0.44/0.69        | ~ (v1_funct_1 @ sk_D_2)
% 0.44/0.69        | ~ (v1_relat_1 @ sk_D_2))),
% 0.44/0.69      inference('sup-', [status(thm)], ['33', '35'])).
% 0.44/0.69  thf('37', plain, ((v1_funct_1 @ sk_D_2)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('38', plain, ((v1_relat_1 @ sk_D_2)),
% 0.44/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.44/0.69  thf('39', plain,
% 0.44/0.69      (((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.44/0.69      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.44/0.69  thf('40', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.44/0.69      inference('demod', [status(thm)], ['32', '39'])).
% 0.44/0.69  thf('41', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.44/0.69      inference('simplify', [status(thm)], ['40'])).
% 0.44/0.69  thf('42', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_D_2 @ 
% 0.44/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0)))),
% 0.44/0.69      inference('demod', [status(thm)], ['5', '41'])).
% 0.44/0.69  thf(dt_k2_relset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.69       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.44/0.69  thf('43', plain,
% 0.44/0.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.69         ((m1_subset_1 @ (k2_relset_1 @ X18 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.44/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.44/0.69      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.44/0.69  thf('44', plain,
% 0.44/0.69      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ k1_xboole_0 @ sk_D_2) @ 
% 0.44/0.69        (k1_zfmisc_1 @ k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.69  thf('45', plain,
% 0.44/0.69      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.44/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.69  thf('46', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.44/0.69      inference('simplify', [status(thm)], ['40'])).
% 0.44/0.69  thf('47', plain,
% 0.44/0.69      (((k2_relset_1 @ sk_B @ k1_xboole_0 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.44/0.69      inference('demod', [status(thm)], ['45', '46'])).
% 0.44/0.69  thf('48', plain,
% 0.44/0.69      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.44/0.69      inference('demod', [status(thm)], ['44', '47'])).
% 0.44/0.69  thf(l3_subset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.44/0.69  thf('49', plain,
% 0.44/0.69      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.69         (~ (r2_hidden @ X1 @ X2)
% 0.44/0.69          | (r2_hidden @ X1 @ X3)
% 0.44/0.69          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.44/0.69      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.44/0.69  thf('50', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.44/0.69          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.44/0.69  thf('51', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.44/0.69      inference('sup-', [status(thm)], ['4', '50'])).
% 0.44/0.69  thf(t7_ordinal1, axiom,
% 0.44/0.69    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.69  thf('52', plain,
% 0.44/0.69      (![X13 : $i, X14 : $i]:
% 0.44/0.69         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.44/0.69      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.44/0.69  thf('53', plain, (~ (r1_tarski @ k1_xboole_0 @ sk_A)),
% 0.44/0.69      inference('sup-', [status(thm)], ['51', '52'])).
% 0.44/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.69  thf('54', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.69  thf('55', plain, ($false), inference('demod', [status(thm)], ['53', '54'])).
% 0.44/0.69  
% 0.44/0.69  % SZS output end Refutation
% 0.44/0.69  
% 0.51/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
