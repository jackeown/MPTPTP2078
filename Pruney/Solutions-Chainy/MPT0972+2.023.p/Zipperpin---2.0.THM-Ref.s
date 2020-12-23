%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IJZY39jMnj

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:36 EST 2020

% Result     : Theorem 2.35s
% Output     : Refutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 600 expanded)
%              Number of leaves         :   40 ( 194 expanded)
%              Depth                    :   23
%              Number of atoms          : 1126 (8691 expanded)
%              Number of equality atoms :   87 ( 421 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('18',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','36'])).

thf('38',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['37','50'])).

thf('52',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['52','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['70','75'])).

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

thf('77',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17 = X16 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X17 ) @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ X17 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('80',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('81',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['70','75'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','81','82','83'])).

thf('85',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['85','88','89'])).

thf('91',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X36: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X36 )
        = ( k1_funct_1 @ sk_D @ X36 ) )
      | ~ ( r2_hidden @ X36 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['93'])).

thf('95',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17 = X16 )
      | ( ( k1_funct_1 @ X17 @ ( sk_C_1 @ X16 @ X17 ) )
       != ( k1_funct_1 @ X16 @ ( sk_C_1 @ X16 @ X17 ) ) )
      | ( ( k1_relat_1 @ X17 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('96',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('98',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['70','75'])).

thf('100',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['37','50'])).

thf('101',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('103',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['96','97','98','99','100','101','102'])).

thf('104',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('107',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IJZY39jMnj
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.35/2.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.35/2.56  % Solved by: fo/fo7.sh
% 2.35/2.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.35/2.56  % done 1224 iterations in 2.097s
% 2.35/2.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.35/2.56  % SZS output start Refutation
% 2.35/2.56  thf(sk_D_type, type, sk_D: $i).
% 2.35/2.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.35/2.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.35/2.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.35/2.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.35/2.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.35/2.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.35/2.56  thf(sk_B_type, type, sk_B: $i > $i).
% 2.35/2.56  thf(sk_A_type, type, sk_A: $i).
% 2.35/2.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.35/2.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.35/2.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.35/2.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.35/2.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.35/2.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.35/2.56  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.35/2.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.35/2.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.35/2.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.35/2.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.35/2.56  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.35/2.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.35/2.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.35/2.56  thf(t18_funct_2, conjecture,
% 2.35/2.56    (![A:$i,B:$i,C:$i]:
% 2.35/2.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.35/2.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.35/2.56       ( ![D:$i]:
% 2.35/2.56         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.35/2.56             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.35/2.56           ( ( ![E:$i]:
% 2.35/2.56               ( ( r2_hidden @ E @ A ) =>
% 2.35/2.56                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.35/2.56             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 2.35/2.56  thf(zf_stmt_0, negated_conjecture,
% 2.35/2.56    (~( ![A:$i,B:$i,C:$i]:
% 2.35/2.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.35/2.56            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.35/2.56          ( ![D:$i]:
% 2.35/2.56            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.35/2.56                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.35/2.56              ( ( ![E:$i]:
% 2.35/2.56                  ( ( r2_hidden @ E @ A ) =>
% 2.35/2.56                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.35/2.56                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 2.35/2.56    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 2.35/2.56  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('1', plain,
% 2.35/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf(redefinition_r2_relset_1, axiom,
% 2.35/2.56    (![A:$i,B:$i,C:$i,D:$i]:
% 2.35/2.56     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.35/2.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.35/2.56       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.35/2.56  thf('2', plain,
% 2.35/2.56      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.35/2.56         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.35/2.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.35/2.56          | (r2_relset_1 @ X25 @ X26 @ X24 @ X27)
% 2.35/2.56          | ((X24) != (X27)))),
% 2.35/2.56      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.35/2.56  thf('3', plain,
% 2.35/2.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.35/2.56         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 2.35/2.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 2.35/2.56      inference('simplify', [status(thm)], ['2'])).
% 2.35/2.56  thf('4', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 2.35/2.56      inference('sup-', [status(thm)], ['1', '3'])).
% 2.35/2.56  thf(d3_tarski, axiom,
% 2.35/2.56    (![A:$i,B:$i]:
% 2.35/2.56     ( ( r1_tarski @ A @ B ) <=>
% 2.35/2.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.35/2.56  thf('5', plain,
% 2.35/2.56      (![X4 : $i, X6 : $i]:
% 2.35/2.56         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.35/2.56      inference('cnf', [status(esa)], [d3_tarski])).
% 2.35/2.56  thf(d1_funct_2, axiom,
% 2.35/2.56    (![A:$i,B:$i,C:$i]:
% 2.35/2.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.35/2.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.35/2.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.35/2.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.35/2.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.35/2.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.35/2.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.35/2.56  thf(zf_stmt_1, axiom,
% 2.35/2.56    (![B:$i,A:$i]:
% 2.35/2.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.35/2.56       ( zip_tseitin_0 @ B @ A ) ))).
% 2.35/2.56  thf('6', plain,
% 2.35/2.56      (![X28 : $i, X29 : $i]:
% 2.35/2.56         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.35/2.56  thf(t113_zfmisc_1, axiom,
% 2.35/2.56    (![A:$i,B:$i]:
% 2.35/2.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.35/2.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.35/2.56  thf('7', plain,
% 2.35/2.56      (![X11 : $i, X12 : $i]:
% 2.35/2.56         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 2.35/2.56          | ((X12) != (k1_xboole_0)))),
% 2.35/2.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.35/2.56  thf('8', plain,
% 2.35/2.56      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 2.35/2.56      inference('simplify', [status(thm)], ['7'])).
% 2.35/2.56  thf('9', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.56         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.35/2.56      inference('sup+', [status(thm)], ['6', '8'])).
% 2.35/2.56  thf('10', plain,
% 2.35/2.56      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf(t5_subset, axiom,
% 2.35/2.56    (![A:$i,B:$i,C:$i]:
% 2.35/2.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.35/2.56          ( v1_xboole_0 @ C ) ) ))).
% 2.35/2.56  thf('11', plain,
% 2.35/2.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.35/2.56         (~ (r2_hidden @ X13 @ X14)
% 2.35/2.56          | ~ (v1_xboole_0 @ X15)
% 2.35/2.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 2.35/2.56      inference('cnf', [status(esa)], [t5_subset])).
% 2.35/2.56  thf('12', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.35/2.56          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 2.35/2.56      inference('sup-', [status(thm)], ['10', '11'])).
% 2.35/2.56  thf('13', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]:
% 2.35/2.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.35/2.56          | (zip_tseitin_0 @ sk_B_1 @ X1)
% 2.35/2.56          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 2.35/2.56      inference('sup-', [status(thm)], ['9', '12'])).
% 2.35/2.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.35/2.56  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.35/2.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.35/2.56  thf('15', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]:
% 2.35/2.56         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 2.35/2.56      inference('demod', [status(thm)], ['13', '14'])).
% 2.35/2.56  thf('16', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]:
% 2.35/2.56         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_0 @ sk_B_1 @ X1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['5', '15'])).
% 2.35/2.56  thf('17', plain,
% 2.35/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.35/2.56  thf(zf_stmt_3, axiom,
% 2.35/2.56    (![C:$i,B:$i,A:$i]:
% 2.35/2.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.35/2.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.35/2.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.35/2.56  thf(zf_stmt_5, axiom,
% 2.35/2.56    (![A:$i,B:$i,C:$i]:
% 2.35/2.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.35/2.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.35/2.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.35/2.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.35/2.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.35/2.56  thf('18', plain,
% 2.35/2.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.35/2.56         (~ (zip_tseitin_0 @ X33 @ X34)
% 2.35/2.56          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 2.35/2.56          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.35/2.56  thf('19', plain,
% 2.35/2.56      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.35/2.56        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.35/2.56      inference('sup-', [status(thm)], ['17', '18'])).
% 2.35/2.56  thf('20', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 2.35/2.56      inference('sup-', [status(thm)], ['16', '19'])).
% 2.35/2.56  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('22', plain,
% 2.35/2.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.35/2.56         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 2.35/2.56          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 2.35/2.56          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.35/2.56  thf('23', plain,
% 2.35/2.56      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.35/2.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['21', '22'])).
% 2.35/2.56  thf('24', plain,
% 2.35/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf(redefinition_k1_relset_1, axiom,
% 2.35/2.56    (![A:$i,B:$i,C:$i]:
% 2.35/2.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.35/2.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.35/2.56  thf('25', plain,
% 2.35/2.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.35/2.56         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 2.35/2.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.35/2.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.35/2.56  thf('26', plain,
% 2.35/2.56      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.35/2.56      inference('sup-', [status(thm)], ['24', '25'])).
% 2.35/2.56  thf('27', plain,
% 2.35/2.56      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.35/2.56        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.35/2.56      inference('demod', [status(thm)], ['23', '26'])).
% 2.35/2.56  thf('28', plain,
% 2.35/2.56      (![X0 : $i]: ((r1_tarski @ sk_C_2 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['20', '27'])).
% 2.35/2.56  thf('29', plain,
% 2.35/2.56      (![X4 : $i, X6 : $i]:
% 2.35/2.56         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.35/2.56      inference('cnf', [status(esa)], [d3_tarski])).
% 2.35/2.56  thf(d1_xboole_0, axiom,
% 2.35/2.56    (![A:$i]:
% 2.35/2.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.35/2.56  thf('30', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.35/2.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.35/2.56  thf('31', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.35/2.56      inference('sup-', [status(thm)], ['29', '30'])).
% 2.35/2.56  thf(d10_xboole_0, axiom,
% 2.35/2.56    (![A:$i,B:$i]:
% 2.35/2.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.35/2.56  thf('32', plain,
% 2.35/2.56      (![X7 : $i, X9 : $i]:
% 2.35/2.56         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.35/2.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.35/2.56  thf('33', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]:
% 2.35/2.56         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['31', '32'])).
% 2.35/2.56  thf('34', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         (((sk_A) = (k1_relat_1 @ sk_D))
% 2.35/2.56          | ((sk_C_2) = (X0))
% 2.35/2.56          | ~ (v1_xboole_0 @ X0))),
% 2.35/2.56      inference('sup-', [status(thm)], ['28', '33'])).
% 2.35/2.56  thf('35', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('36', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 2.35/2.56          | ~ (v1_xboole_0 @ X0)
% 2.35/2.56          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['34', '35'])).
% 2.35/2.56  thf('37', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | ~ (v1_xboole_0 @ sk_D))),
% 2.35/2.56      inference('sup-', [status(thm)], ['4', '36'])).
% 2.35/2.56  thf('38', plain,
% 2.35/2.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.35/2.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.35/2.56  thf('39', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.56         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.35/2.56      inference('sup+', [status(thm)], ['6', '8'])).
% 2.35/2.56  thf('40', plain,
% 2.35/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('41', plain,
% 2.35/2.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.35/2.56         (~ (r2_hidden @ X13 @ X14)
% 2.35/2.56          | ~ (v1_xboole_0 @ X15)
% 2.35/2.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 2.35/2.56      inference('cnf', [status(esa)], [t5_subset])).
% 2.35/2.56  thf('42', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.35/2.56          | ~ (r2_hidden @ X0 @ sk_D))),
% 2.35/2.56      inference('sup-', [status(thm)], ['40', '41'])).
% 2.35/2.56  thf('43', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]:
% 2.35/2.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.35/2.56          | (zip_tseitin_0 @ sk_B_1 @ X1)
% 2.35/2.56          | ~ (r2_hidden @ X0 @ sk_D))),
% 2.35/2.56      inference('sup-', [status(thm)], ['39', '42'])).
% 2.35/2.56  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.35/2.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.35/2.56  thf('45', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]:
% 2.35/2.56         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_D))),
% 2.35/2.56      inference('demod', [status(thm)], ['43', '44'])).
% 2.35/2.56  thf('46', plain,
% 2.35/2.56      (![X0 : $i]: ((v1_xboole_0 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 2.35/2.56      inference('sup-', [status(thm)], ['38', '45'])).
% 2.35/2.56  thf('47', plain,
% 2.35/2.56      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.35/2.56        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.35/2.56      inference('sup-', [status(thm)], ['17', '18'])).
% 2.35/2.56  thf('48', plain,
% 2.35/2.56      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 2.35/2.56      inference('sup-', [status(thm)], ['46', '47'])).
% 2.35/2.56  thf('49', plain,
% 2.35/2.56      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.35/2.56        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.35/2.56      inference('demod', [status(thm)], ['23', '26'])).
% 2.35/2.56  thf('50', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['48', '49'])).
% 2.35/2.56  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.35/2.56      inference('clc', [status(thm)], ['37', '50'])).
% 2.35/2.56  thf('52', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 2.35/2.56      inference('sup-', [status(thm)], ['1', '3'])).
% 2.35/2.56  thf('53', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]:
% 2.35/2.56         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_0 @ sk_B_1 @ X1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['5', '15'])).
% 2.35/2.56  thf('54', plain,
% 2.35/2.56      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('55', plain,
% 2.35/2.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.35/2.56         (~ (zip_tseitin_0 @ X33 @ X34)
% 2.35/2.56          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 2.35/2.56          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.35/2.56  thf('56', plain,
% 2.35/2.56      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.35/2.56        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.35/2.56      inference('sup-', [status(thm)], ['54', '55'])).
% 2.35/2.56  thf('57', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 2.35/2.56      inference('sup-', [status(thm)], ['53', '56'])).
% 2.35/2.56  thf('58', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('59', plain,
% 2.35/2.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.35/2.56         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 2.35/2.56          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 2.35/2.56          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.35/2.56  thf('60', plain,
% 2.35/2.56      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.35/2.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['58', '59'])).
% 2.35/2.56  thf('61', plain,
% 2.35/2.56      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('62', plain,
% 2.35/2.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.35/2.56         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 2.35/2.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.35/2.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.35/2.56  thf('63', plain,
% 2.35/2.56      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 2.35/2.56      inference('sup-', [status(thm)], ['61', '62'])).
% 2.35/2.56  thf('64', plain,
% 2.35/2.56      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.35/2.56        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.35/2.56      inference('demod', [status(thm)], ['60', '63'])).
% 2.35/2.56  thf('65', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         ((r1_tarski @ sk_C_2 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['57', '64'])).
% 2.35/2.56  thf('66', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]:
% 2.35/2.56         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['31', '32'])).
% 2.35/2.56  thf('67', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 2.35/2.56          | ((sk_C_2) = (X0))
% 2.35/2.56          | ~ (v1_xboole_0 @ X0))),
% 2.35/2.56      inference('sup-', [status(thm)], ['65', '66'])).
% 2.35/2.56  thf('68', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('69', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 2.35/2.56          | ~ (v1_xboole_0 @ X0)
% 2.35/2.56          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['67', '68'])).
% 2.35/2.56  thf('70', plain,
% 2.35/2.56      ((((sk_A) = (k1_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ sk_D))),
% 2.35/2.56      inference('sup-', [status(thm)], ['52', '69'])).
% 2.35/2.56  thf('71', plain,
% 2.35/2.56      (![X0 : $i]: ((v1_xboole_0 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 2.35/2.56      inference('sup-', [status(thm)], ['38', '45'])).
% 2.35/2.56  thf('72', plain,
% 2.35/2.56      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.35/2.56        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.35/2.56      inference('sup-', [status(thm)], ['54', '55'])).
% 2.35/2.56  thf('73', plain,
% 2.35/2.56      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 2.35/2.56      inference('sup-', [status(thm)], ['71', '72'])).
% 2.35/2.56  thf('74', plain,
% 2.35/2.56      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.35/2.56        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.35/2.56      inference('demod', [status(thm)], ['60', '63'])).
% 2.35/2.56  thf('75', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['73', '74'])).
% 2.35/2.56  thf('76', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.35/2.56      inference('clc', [status(thm)], ['70', '75'])).
% 2.35/2.56  thf(t9_funct_1, axiom,
% 2.35/2.56    (![A:$i]:
% 2.35/2.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.35/2.56       ( ![B:$i]:
% 2.35/2.56         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.35/2.56           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.35/2.56               ( ![C:$i]:
% 2.35/2.56                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 2.35/2.56                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 2.35/2.56             ( ( A ) = ( B ) ) ) ) ) ))).
% 2.35/2.56  thf('77', plain,
% 2.35/2.56      (![X16 : $i, X17 : $i]:
% 2.35/2.56         (~ (v1_relat_1 @ X16)
% 2.35/2.56          | ~ (v1_funct_1 @ X16)
% 2.35/2.56          | ((X17) = (X16))
% 2.35/2.56          | (r2_hidden @ (sk_C_1 @ X16 @ X17) @ (k1_relat_1 @ X17))
% 2.35/2.56          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 2.35/2.56          | ~ (v1_funct_1 @ X17)
% 2.35/2.56          | ~ (v1_relat_1 @ X17))),
% 2.35/2.56      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.35/2.56  thf('78', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         (((sk_A) != (k1_relat_1 @ X0))
% 2.35/2.56          | ~ (v1_relat_1 @ sk_C_2)
% 2.35/2.56          | ~ (v1_funct_1 @ sk_C_2)
% 2.35/2.56          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 2.35/2.56          | ((sk_C_2) = (X0))
% 2.35/2.56          | ~ (v1_funct_1 @ X0)
% 2.35/2.56          | ~ (v1_relat_1 @ X0))),
% 2.35/2.56      inference('sup-', [status(thm)], ['76', '77'])).
% 2.35/2.56  thf('79', plain,
% 2.35/2.56      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf(cc1_relset_1, axiom,
% 2.35/2.56    (![A:$i,B:$i,C:$i]:
% 2.35/2.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.35/2.56       ( v1_relat_1 @ C ) ))).
% 2.35/2.56  thf('80', plain,
% 2.35/2.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.35/2.56         ((v1_relat_1 @ X18)
% 2.35/2.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.35/2.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.35/2.56  thf('81', plain, ((v1_relat_1 @ sk_C_2)),
% 2.35/2.56      inference('sup-', [status(thm)], ['79', '80'])).
% 2.35/2.56  thf('82', plain, ((v1_funct_1 @ sk_C_2)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('83', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.35/2.56      inference('clc', [status(thm)], ['70', '75'])).
% 2.35/2.56  thf('84', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         (((sk_A) != (k1_relat_1 @ X0))
% 2.35/2.56          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 2.35/2.56          | ((sk_C_2) = (X0))
% 2.35/2.56          | ~ (v1_funct_1 @ X0)
% 2.35/2.56          | ~ (v1_relat_1 @ X0))),
% 2.35/2.56      inference('demod', [status(thm)], ['78', '81', '82', '83'])).
% 2.35/2.56  thf('85', plain,
% 2.35/2.56      ((((sk_A) != (sk_A))
% 2.35/2.56        | ~ (v1_relat_1 @ sk_D)
% 2.35/2.56        | ~ (v1_funct_1 @ sk_D)
% 2.35/2.56        | ((sk_C_2) = (sk_D))
% 2.35/2.56        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 2.35/2.56      inference('sup-', [status(thm)], ['51', '84'])).
% 2.35/2.56  thf('86', plain,
% 2.35/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('87', plain,
% 2.35/2.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.35/2.56         ((v1_relat_1 @ X18)
% 2.35/2.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.35/2.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.35/2.56  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 2.35/2.56      inference('sup-', [status(thm)], ['86', '87'])).
% 2.35/2.56  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('90', plain,
% 2.35/2.56      ((((sk_A) != (sk_A))
% 2.35/2.56        | ((sk_C_2) = (sk_D))
% 2.35/2.56        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 2.35/2.56      inference('demod', [status(thm)], ['85', '88', '89'])).
% 2.35/2.56  thf('91', plain,
% 2.35/2.56      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 2.35/2.56      inference('simplify', [status(thm)], ['90'])).
% 2.35/2.56  thf('92', plain,
% 2.35/2.56      (![X36 : $i]:
% 2.35/2.56         (((k1_funct_1 @ sk_C_2 @ X36) = (k1_funct_1 @ sk_D @ X36))
% 2.35/2.56          | ~ (r2_hidden @ X36 @ sk_A))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('93', plain,
% 2.35/2.56      ((((sk_C_2) = (sk_D))
% 2.35/2.56        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.35/2.56            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 2.35/2.56      inference('sup-', [status(thm)], ['91', '92'])).
% 2.35/2.56  thf('94', plain,
% 2.35/2.56      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.35/2.56         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 2.35/2.56      inference('condensation', [status(thm)], ['93'])).
% 2.35/2.56  thf('95', plain,
% 2.35/2.56      (![X16 : $i, X17 : $i]:
% 2.35/2.56         (~ (v1_relat_1 @ X16)
% 2.35/2.56          | ~ (v1_funct_1 @ X16)
% 2.35/2.56          | ((X17) = (X16))
% 2.35/2.56          | ((k1_funct_1 @ X17 @ (sk_C_1 @ X16 @ X17))
% 2.35/2.56              != (k1_funct_1 @ X16 @ (sk_C_1 @ X16 @ X17)))
% 2.35/2.56          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 2.35/2.56          | ~ (v1_funct_1 @ X17)
% 2.35/2.56          | ~ (v1_relat_1 @ X17))),
% 2.35/2.56      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.35/2.56  thf('96', plain,
% 2.35/2.56      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.35/2.56          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 2.35/2.56        | ~ (v1_relat_1 @ sk_C_2)
% 2.35/2.56        | ~ (v1_funct_1 @ sk_C_2)
% 2.35/2.56        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 2.35/2.56        | ((sk_C_2) = (sk_D))
% 2.35/2.56        | ~ (v1_funct_1 @ sk_D)
% 2.35/2.56        | ~ (v1_relat_1 @ sk_D))),
% 2.35/2.56      inference('sup-', [status(thm)], ['94', '95'])).
% 2.35/2.56  thf('97', plain, ((v1_relat_1 @ sk_C_2)),
% 2.35/2.56      inference('sup-', [status(thm)], ['79', '80'])).
% 2.35/2.56  thf('98', plain, ((v1_funct_1 @ sk_C_2)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('99', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.35/2.56      inference('clc', [status(thm)], ['70', '75'])).
% 2.35/2.56  thf('100', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.35/2.56      inference('clc', [status(thm)], ['37', '50'])).
% 2.35/2.56  thf('101', plain, ((v1_funct_1 @ sk_D)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('102', plain, ((v1_relat_1 @ sk_D)),
% 2.35/2.56      inference('sup-', [status(thm)], ['86', '87'])).
% 2.35/2.56  thf('103', plain,
% 2.35/2.56      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.35/2.56          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 2.35/2.56        | ((sk_A) != (sk_A))
% 2.35/2.56        | ((sk_C_2) = (sk_D)))),
% 2.35/2.56      inference('demod', [status(thm)],
% 2.35/2.56                ['96', '97', '98', '99', '100', '101', '102'])).
% 2.35/2.56  thf('104', plain, (((sk_C_2) = (sk_D))),
% 2.35/2.56      inference('simplify', [status(thm)], ['103'])).
% 2.35/2.56  thf('105', plain,
% 2.35/2.56      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('106', plain,
% 2.35/2.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.35/2.56         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 2.35/2.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 2.35/2.56      inference('simplify', [status(thm)], ['2'])).
% 2.35/2.56  thf('107', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 2.35/2.56      inference('sup-', [status(thm)], ['105', '106'])).
% 2.35/2.56  thf('108', plain, ($false),
% 2.35/2.56      inference('demod', [status(thm)], ['0', '104', '107'])).
% 2.35/2.56  
% 2.35/2.56  % SZS output end Refutation
% 2.35/2.56  
% 2.35/2.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
