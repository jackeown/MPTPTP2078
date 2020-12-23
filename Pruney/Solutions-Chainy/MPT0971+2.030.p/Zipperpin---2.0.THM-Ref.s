%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sUUCGaHIAq

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 227 expanded)
%              Number of leaves         :   37 (  82 expanded)
%              Depth                    :   17
%              Number of atoms          :  625 (2725 expanded)
%              Number of equality atoms :   45 ( 147 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

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
    r2_hidden @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
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
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( sk_D_1 @ X14 @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('21',plain,(
    ! [X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( sk_D_1 @ X14 @ X11 ) @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_2 @ X34 )
       != sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) )
     != sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('34',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k2_relat_1 @ X11 ) )
      | ( X14
        = ( k1_funct_1 @ X11 @ ( sk_D_1 @ X14 @ X11 ) ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('35',plain,(
    ! [X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X11 ) )
      | ( X14
        = ( k1_funct_1 @ X11 @ ( sk_D_1 @ X14 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['26','27'])).

thf('39',plain,
    ( sk_C_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 != sk_C_1 ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','41'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('44',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('46',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_2 )
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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ sk_C_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','50'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sUUCGaHIAq
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:51:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.67  % Solved by: fo/fo7.sh
% 0.20/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.67  % done 155 iterations in 0.215s
% 0.20/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.67  % SZS output start Refutation
% 0.20/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.67  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.67  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.67  thf(t17_funct_2, conjecture,
% 0.20/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.67       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.67            ( ![E:$i]:
% 0.20/0.67              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.20/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.67            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.67          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.67               ( ![E:$i]:
% 0.20/0.67                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.20/0.67                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.20/0.67    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.20/0.67  thf('0', plain,
% 0.20/0.67      ((r2_hidden @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2))),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.67  thf('1', plain,
% 0.20/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.67    (![A:$i,B:$i,C:$i]:
% 0.20/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.67  thf('2', plain,
% 0.20/0.67      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.67         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.20/0.67          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.67  thf('3', plain,
% 0.20/0.67      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.20/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.67  thf('4', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.20/0.67      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.67  thf('5', plain,
% 0.20/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.67  thf(d1_funct_2, axiom,
% 0.20/0.67    (![A:$i,B:$i,C:$i]:
% 0.20/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.67  thf(zf_stmt_1, axiom,
% 0.20/0.67    (![B:$i,A:$i]:
% 0.20/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.67  thf('6', plain,
% 0.20/0.67      (![X26 : $i, X27 : $i]:
% 0.20/0.67         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.67  thf('7', plain,
% 0.20/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.67  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.67  thf(zf_stmt_3, axiom,
% 0.20/0.67    (![C:$i,B:$i,A:$i]:
% 0.20/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.67  thf(zf_stmt_5, axiom,
% 0.20/0.67    (![A:$i,B:$i,C:$i]:
% 0.20/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.67  thf('8', plain,
% 0.20/0.67      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.67         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.20/0.67          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.20/0.67          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.67  thf('9', plain,
% 0.20/0.67      (((zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.20/0.67        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.20/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.67  thf('10', plain,
% 0.20/0.67      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A))),
% 0.20/0.67      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.67  thf('11', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1)),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.67  thf('12', plain,
% 0.20/0.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.67         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.20/0.67          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.20/0.67          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.67  thf('13', plain,
% 0.20/0.67      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.20/0.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 0.20/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.67  thf('14', plain,
% 0.20/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.67    (![A:$i,B:$i,C:$i]:
% 0.20/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.67  thf('15', plain,
% 0.20/0.67      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.67         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.20/0.67          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.67  thf('16', plain,
% 0.20/0.67      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.20/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.67  thf('17', plain,
% 0.20/0.67      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.20/0.67        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.20/0.67      inference('demod', [status(thm)], ['13', '16'])).
% 0.20/0.67  thf('18', plain,
% 0.20/0.67      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.20/0.67      inference('sup-', [status(thm)], ['10', '17'])).
% 0.20/0.67  thf('19', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.20/0.67      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.67  thf(d5_funct_1, axiom,
% 0.20/0.67    (![A:$i]:
% 0.20/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.67       ( ![B:$i]:
% 0.20/0.67         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.67           ( ![C:$i]:
% 0.20/0.67             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.67               ( ?[D:$i]:
% 0.20/0.67                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.67                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.67  thf('20', plain,
% 0.20/0.67      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.20/0.67         (((X13) != (k2_relat_1 @ X11))
% 0.20/0.67          | (r2_hidden @ (sk_D_1 @ X14 @ X11) @ (k1_relat_1 @ X11))
% 0.20/0.67          | ~ (r2_hidden @ X14 @ X13)
% 0.20/0.67          | ~ (v1_funct_1 @ X11)
% 0.20/0.67          | ~ (v1_relat_1 @ X11))),
% 0.20/0.67      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.67  thf('21', plain,
% 0.20/0.67      (![X11 : $i, X14 : $i]:
% 0.20/0.67         (~ (v1_relat_1 @ X11)
% 0.20/0.67          | ~ (v1_funct_1 @ X11)
% 0.20/0.67          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X11))
% 0.20/0.67          | (r2_hidden @ (sk_D_1 @ X14 @ X11) @ (k1_relat_1 @ X11)))),
% 0.20/0.67      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.67  thf('22', plain,
% 0.20/0.67      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.20/0.67        | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.67        | ~ (v1_relat_1 @ sk_D_2))),
% 0.20/0.67      inference('sup-', [status(thm)], ['19', '21'])).
% 0.20/0.67  thf('23', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.67  thf('24', plain,
% 0.20/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.67  thf(cc2_relat_1, axiom,
% 0.20/0.67    (![A:$i]:
% 0.20/0.67     ( ( v1_relat_1 @ A ) =>
% 0.20/0.67       ( ![B:$i]:
% 0.20/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.67  thf('25', plain,
% 0.20/0.67      (![X6 : $i, X7 : $i]:
% 0.20/0.67         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.67          | (v1_relat_1 @ X6)
% 0.20/0.67          | ~ (v1_relat_1 @ X7))),
% 0.20/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.67  thf('26', plain,
% 0.20/0.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_2))),
% 0.20/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.67  thf(fc6_relat_1, axiom,
% 0.20/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.67  thf('27', plain,
% 0.20/0.67      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.20/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.67  thf('28', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.67      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.67  thf('29', plain,
% 0.20/0.67      ((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.20/0.67      inference('demod', [status(thm)], ['22', '23', '28'])).
% 0.20/0.67  thf('30', plain,
% 0.20/0.67      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ sk_A)
% 0.20/0.67        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.67      inference('sup+', [status(thm)], ['18', '29'])).
% 0.20/0.67  thf('31', plain,
% 0.20/0.67      (![X34 : $i]:
% 0.20/0.67         (~ (r2_hidden @ X34 @ sk_A)
% 0.20/0.67          | ((k1_funct_1 @ sk_D_2 @ X34) != (sk_C_1)))),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.67  thf('32', plain,
% 0.20/0.67      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.67        | ((k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)) != (sk_C_1)))),
% 0.20/0.67      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.67  thf('33', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.20/0.67      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.67  thf('34', plain,
% 0.20/0.67      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.20/0.67         (((X13) != (k2_relat_1 @ X11))
% 0.20/0.67          | ((X14) = (k1_funct_1 @ X11 @ (sk_D_1 @ X14 @ X11)))
% 0.20/0.67          | ~ (r2_hidden @ X14 @ X13)
% 0.20/0.67          | ~ (v1_funct_1 @ X11)
% 0.20/0.67          | ~ (v1_relat_1 @ X11))),
% 0.20/0.67      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.67  thf('35', plain,
% 0.20/0.67      (![X11 : $i, X14 : $i]:
% 0.20/0.67         (~ (v1_relat_1 @ X11)
% 0.20/0.67          | ~ (v1_funct_1 @ X11)
% 0.20/0.67          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X11))
% 0.20/0.67          | ((X14) = (k1_funct_1 @ X11 @ (sk_D_1 @ X14 @ X11))))),
% 0.20/0.67      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.67  thf('36', plain,
% 0.20/0.67      ((((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))
% 0.20/0.67        | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.67        | ~ (v1_relat_1 @ sk_D_2))),
% 0.20/0.67      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.67  thf('37', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.67  thf('38', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.67      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.67  thf('39', plain,
% 0.20/0.67      (((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))),
% 0.20/0.67      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.20/0.67  thf('40', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C_1) != (sk_C_1)))),
% 0.20/0.67      inference('demod', [status(thm)], ['32', '39'])).
% 0.20/0.67  thf('41', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.67      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.67  thf('42', plain,
% 0.20/0.67      ((m1_subset_1 @ sk_D_2 @ 
% 0.20/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.20/0.67      inference('demod', [status(thm)], ['5', '41'])).
% 0.20/0.67  thf(dt_k2_relset_1, axiom,
% 0.20/0.67    (![A:$i,B:$i,C:$i]:
% 0.20/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.67       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.67  thf('43', plain,
% 0.20/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.67         ((m1_subset_1 @ (k2_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 0.20/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.67      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.67  thf('44', plain,
% 0.20/0.67      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_2) @ 
% 0.20/0.67        (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.68  thf('45', plain,
% 0.20/0.68      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.20/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.68  thf('46', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.68      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.68  thf('47', plain,
% 0.20/0.68      (((k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.20/0.68      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.68  thf('48', plain,
% 0.20/0.68      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.68      inference('demod', [status(thm)], ['44', '47'])).
% 0.20/0.68  thf(l3_subset_1, axiom,
% 0.20/0.68    (![A:$i,B:$i]:
% 0.20/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.68  thf('49', plain,
% 0.20/0.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.68         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.68          | (r2_hidden @ X3 @ X5)
% 0.20/0.68          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.68      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.68  thf('50', plain,
% 0.20/0.68      (![X0 : $i]:
% 0.20/0.68         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.68          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.20/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.68  thf('51', plain, ((r2_hidden @ sk_C_1 @ k1_xboole_0)),
% 0.20/0.68      inference('sup-', [status(thm)], ['4', '50'])).
% 0.20/0.68  thf(d1_xboole_0, axiom,
% 0.20/0.68    (![A:$i]:
% 0.20/0.68     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.68  thf('52', plain,
% 0.20/0.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.68  thf('53', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.68      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.68  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.68  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.68  thf('55', plain, ($false), inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.68  
% 0.20/0.68  % SZS output end Refutation
% 0.20/0.68  
% 0.20/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
