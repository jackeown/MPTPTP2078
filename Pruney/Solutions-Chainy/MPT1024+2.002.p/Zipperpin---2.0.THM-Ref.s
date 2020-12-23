%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hcDJJFzJqc

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:33 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 186 expanded)
%              Number of leaves         :   44 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :  769 (2192 expanded)
%              Number of equality atoms :   44 (  89 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( sk_D_2 @ X21 @ X19 @ X20 ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1 ),
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

thf('12',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X14: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('29',plain,(
    r2_hidden @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X5 @ X3 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k3_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_tarski @ X4 ) )
      | ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_B @ sk_D_3 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('35',plain,(
    ! [X13: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_B @ sk_D_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_D_3 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['24','38'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X21 @ X19 @ X20 ) @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('46',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['20','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['17','50'])).

thf('52',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference(demod,[status(thm)],['10','51'])).

thf('53',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_A )
      | ~ ( r2_hidden @ X43 @ sk_C_1 )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_3 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( sk_D_2 @ X21 @ X19 @ X20 ) @ X19 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('59',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    sk_E
 != ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('61',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ),
    inference(demod,[status(thm)],['44','45'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('62',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('65',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['60','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hcDJJFzJqc
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:55:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.73/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.73/0.91  % Solved by: fo/fo7.sh
% 0.73/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.73/0.91  % done 354 iterations in 0.472s
% 0.73/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.73/0.91  % SZS output start Refutation
% 0.73/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.73/0.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.73/0.91  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.73/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.73/0.91  thf(sk_B_type, type, sk_B: $i > $i).
% 0.73/0.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.73/0.91  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.73/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.73/0.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.73/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.73/0.91  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.73/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.73/0.91  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.73/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.73/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.73/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.73/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.73/0.91  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.73/0.91  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.73/0.91  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.73/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.73/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.73/0.91  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.73/0.91  thf(sk_E_type, type, sk_E: $i).
% 0.73/0.91  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.73/0.91  thf(t115_funct_2, conjecture,
% 0.73/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.91     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.73/0.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.73/0.91       ( ![E:$i]:
% 0.73/0.91         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.73/0.91              ( ![F:$i]:
% 0.73/0.91                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.73/0.91                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.73/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.73/0.91    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.91        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.73/0.91            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.73/0.91          ( ![E:$i]:
% 0.73/0.91            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.73/0.91                 ( ![F:$i]:
% 0.73/0.91                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.73/0.91                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.73/0.91    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.73/0.91  thf('0', plain,
% 0.73/0.91      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ sk_C_1))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('1', plain,
% 0.73/0.91      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf(redefinition_k7_relset_1, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.73/0.91       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.73/0.91  thf('2', plain,
% 0.73/0.91      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.73/0.91          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 0.73/0.91      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.73/0.91  thf('3', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ X0)
% 0.73/0.91           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.73/0.91      inference('sup-', [status(thm)], ['1', '2'])).
% 0.73/0.91  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.73/0.91      inference('demod', [status(thm)], ['0', '3'])).
% 0.73/0.91  thf(t143_relat_1, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i]:
% 0.73/0.91     ( ( v1_relat_1 @ C ) =>
% 0.73/0.91       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.73/0.91         ( ?[D:$i]:
% 0.73/0.91           ( ( r2_hidden @ D @ B ) & 
% 0.73/0.91             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.73/0.91             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.73/0.91  thf('5', plain,
% 0.73/0.91      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.73/0.91         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 0.73/0.91          | (r2_hidden @ (sk_D_2 @ X21 @ X19 @ X20) @ (k1_relat_1 @ X21))
% 0.73/0.91          | ~ (v1_relat_1 @ X21))),
% 0.73/0.91      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.73/0.91  thf('6', plain,
% 0.73/0.91      ((~ (v1_relat_1 @ sk_D_3)
% 0.73/0.91        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ 
% 0.73/0.91           (k1_relat_1 @ sk_D_3)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['4', '5'])).
% 0.73/0.91  thf('7', plain,
% 0.73/0.91      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf(cc1_relset_1, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i]:
% 0.73/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.73/0.91       ( v1_relat_1 @ C ) ))).
% 0.73/0.91  thf('8', plain,
% 0.73/0.91      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.73/0.91         ((v1_relat_1 @ X25)
% 0.73/0.91          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.73/0.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.73/0.91  thf('9', plain, ((v1_relat_1 @ sk_D_3)),
% 0.73/0.91      inference('sup-', [status(thm)], ['7', '8'])).
% 0.73/0.91  thf('10', plain,
% 0.73/0.91      ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 0.73/0.91      inference('demod', [status(thm)], ['6', '9'])).
% 0.73/0.91  thf('11', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1)),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf(d1_funct_2, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i]:
% 0.73/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.73/0.91       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.73/0.91           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.73/0.91             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.73/0.91         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.73/0.91           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.73/0.91             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.73/0.91  thf(zf_stmt_1, axiom,
% 0.73/0.91    (![C:$i,B:$i,A:$i]:
% 0.73/0.91     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.73/0.91       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.73/0.91  thf('12', plain,
% 0.73/0.91      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.73/0.91         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.73/0.91          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.73/0.91          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.73/0.91  thf('13', plain,
% 0.73/0.91      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.73/0.91        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['11', '12'])).
% 0.73/0.91  thf('14', plain,
% 0.73/0.91      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf(redefinition_k1_relset_1, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i]:
% 0.73/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.73/0.91       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.73/0.91  thf('15', plain,
% 0.73/0.91      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.73/0.91         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.73/0.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.73/0.91      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.73/0.91  thf('16', plain,
% 0.73/0.91      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.73/0.91      inference('sup-', [status(thm)], ['14', '15'])).
% 0.73/0.91  thf('17', plain,
% 0.73/0.91      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.73/0.91        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.73/0.91      inference('demod', [status(thm)], ['13', '16'])).
% 0.73/0.91  thf('18', plain,
% 0.73/0.91      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.73/0.91  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.73/0.91  thf(zf_stmt_4, axiom,
% 0.73/0.91    (![B:$i,A:$i]:
% 0.73/0.91     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.73/0.91       ( zip_tseitin_0 @ B @ A ) ))).
% 0.73/0.91  thf(zf_stmt_5, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i]:
% 0.73/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.73/0.91       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.73/0.91         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.73/0.91           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.73/0.91             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.73/0.91  thf('19', plain,
% 0.73/0.91      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.73/0.91         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.73/0.91          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.73/0.91          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.73/0.91  thf('20', plain,
% 0.73/0.91      (((zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.73/0.91        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.73/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.73/0.91  thf('21', plain,
% 0.73/0.91      (![X35 : $i, X36 : $i]:
% 0.73/0.91         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.73/0.91  thf(t113_zfmisc_1, axiom,
% 0.73/0.91    (![A:$i,B:$i]:
% 0.73/0.91     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.73/0.91       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.73/0.91  thf('22', plain,
% 0.73/0.91      (![X11 : $i, X12 : $i]:
% 0.73/0.91         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.73/0.91          | ((X12) != (k1_xboole_0)))),
% 0.73/0.91      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.73/0.91  thf('23', plain,
% 0.73/0.91      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.73/0.91      inference('simplify', [status(thm)], ['22'])).
% 0.73/0.91  thf('24', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.91         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.73/0.91      inference('sup+', [status(thm)], ['21', '23'])).
% 0.73/0.91  thf('25', plain,
% 0.73/0.91      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf(t2_subset, axiom,
% 0.73/0.91    (![A:$i,B:$i]:
% 0.73/0.91     ( ( m1_subset_1 @ A @ B ) =>
% 0.73/0.91       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.73/0.91  thf('26', plain,
% 0.73/0.91      (![X15 : $i, X16 : $i]:
% 0.73/0.91         ((r2_hidden @ X15 @ X16)
% 0.73/0.91          | (v1_xboole_0 @ X16)
% 0.73/0.91          | ~ (m1_subset_1 @ X15 @ X16))),
% 0.73/0.91      inference('cnf', [status(esa)], [t2_subset])).
% 0.73/0.91  thf('27', plain,
% 0.73/0.91      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.73/0.91        | (r2_hidden @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.73/0.91      inference('sup-', [status(thm)], ['25', '26'])).
% 0.73/0.91  thf(fc1_subset_1, axiom,
% 0.73/0.91    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.73/0.91  thf('28', plain, (![X14 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.73/0.91      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.73/0.91  thf('29', plain,
% 0.73/0.91      ((r2_hidden @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.73/0.91      inference('clc', [status(thm)], ['27', '28'])).
% 0.73/0.91  thf(d1_xboole_0, axiom,
% 0.73/0.91    (![A:$i]:
% 0.73/0.91     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.73/0.91  thf('30', plain,
% 0.73/0.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.73/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.73/0.91  thf(d4_tarski, axiom,
% 0.73/0.91    (![A:$i,B:$i]:
% 0.73/0.91     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.73/0.91       ( ![C:$i]:
% 0.73/0.91         ( ( r2_hidden @ C @ B ) <=>
% 0.73/0.91           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.73/0.91  thf('31', plain,
% 0.73/0.91      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.73/0.91         (~ (r2_hidden @ X3 @ X4)
% 0.73/0.91          | ~ (r2_hidden @ X5 @ X3)
% 0.73/0.91          | (r2_hidden @ X5 @ X6)
% 0.73/0.91          | ((X6) != (k3_tarski @ X4)))),
% 0.73/0.91      inference('cnf', [status(esa)], [d4_tarski])).
% 0.73/0.91  thf('32', plain,
% 0.73/0.91      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.73/0.91         ((r2_hidden @ X5 @ (k3_tarski @ X4))
% 0.73/0.91          | ~ (r2_hidden @ X5 @ X3)
% 0.73/0.91          | ~ (r2_hidden @ X3 @ X4))),
% 0.73/0.91      inference('simplify', [status(thm)], ['31'])).
% 0.73/0.91  thf('33', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i]:
% 0.73/0.91         ((v1_xboole_0 @ X0)
% 0.73/0.91          | ~ (r2_hidden @ X0 @ X1)
% 0.73/0.91          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['30', '32'])).
% 0.73/0.91  thf('34', plain,
% 0.73/0.91      (((r2_hidden @ (sk_B @ sk_D_3) @ 
% 0.73/0.91         (k3_tarski @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.73/0.91        | (v1_xboole_0 @ sk_D_3))),
% 0.73/0.91      inference('sup-', [status(thm)], ['29', '33'])).
% 0.73/0.91  thf(t99_zfmisc_1, axiom,
% 0.73/0.91    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.73/0.91  thf('35', plain, (![X13 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X13)) = (X13))),
% 0.73/0.91      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.73/0.91  thf('36', plain,
% 0.73/0.91      (((r2_hidden @ (sk_B @ sk_D_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.73/0.91        | (v1_xboole_0 @ sk_D_3))),
% 0.73/0.91      inference('demod', [status(thm)], ['34', '35'])).
% 0.73/0.91  thf('37', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.73/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.73/0.91  thf('38', plain,
% 0.73/0.91      (((v1_xboole_0 @ sk_D_3)
% 0.73/0.91        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['36', '37'])).
% 0.73/0.91  thf('39', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.73/0.91          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 0.73/0.91          | (v1_xboole_0 @ sk_D_3))),
% 0.73/0.91      inference('sup-', [status(thm)], ['24', '38'])).
% 0.73/0.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.73/0.91  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.73/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.73/0.91  thf('41', plain,
% 0.73/0.91      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D_3))),
% 0.73/0.91      inference('demod', [status(thm)], ['39', '40'])).
% 0.73/0.91  thf('42', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.73/0.91      inference('demod', [status(thm)], ['0', '3'])).
% 0.73/0.91  thf('43', plain,
% 0.73/0.91      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.73/0.91         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 0.73/0.91          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X21 @ X19 @ X20) @ X20) @ X21)
% 0.73/0.91          | ~ (v1_relat_1 @ X21))),
% 0.73/0.91      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.73/0.91  thf('44', plain,
% 0.73/0.91      ((~ (v1_relat_1 @ sk_D_3)
% 0.73/0.91        | (r2_hidden @ 
% 0.73/0.91           (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ sk_D_3))),
% 0.73/0.91      inference('sup-', [status(thm)], ['42', '43'])).
% 0.73/0.91  thf('45', plain, ((v1_relat_1 @ sk_D_3)),
% 0.73/0.91      inference('sup-', [status(thm)], ['7', '8'])).
% 0.73/0.91  thf('46', plain,
% 0.73/0.91      ((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.73/0.91        sk_D_3)),
% 0.73/0.91      inference('demod', [status(thm)], ['44', '45'])).
% 0.73/0.91  thf('47', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.73/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.73/0.91  thf('48', plain, (~ (v1_xboole_0 @ sk_D_3)),
% 0.73/0.91      inference('sup-', [status(thm)], ['46', '47'])).
% 0.73/0.91  thf('49', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.73/0.91      inference('sup-', [status(thm)], ['41', '48'])).
% 0.73/0.91  thf('50', plain, ((zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)),
% 0.73/0.91      inference('demod', [status(thm)], ['20', '49'])).
% 0.73/0.91  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 0.73/0.91      inference('demod', [status(thm)], ['17', '50'])).
% 0.73/0.91  thf('52', plain, ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A)),
% 0.73/0.91      inference('demod', [status(thm)], ['10', '51'])).
% 0.73/0.91  thf('53', plain,
% 0.73/0.91      (![X43 : $i]:
% 0.73/0.91         (~ (r2_hidden @ X43 @ sk_A)
% 0.73/0.91          | ~ (r2_hidden @ X43 @ sk_C_1)
% 0.73/0.91          | ((sk_E) != (k1_funct_1 @ sk_D_3 @ X43)))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('54', plain,
% 0.73/0.91      ((((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E)))
% 0.73/0.91        | ~ (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.73/0.91      inference('sup-', [status(thm)], ['52', '53'])).
% 0.73/0.91  thf('55', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.73/0.91      inference('demod', [status(thm)], ['0', '3'])).
% 0.73/0.91  thf('56', plain,
% 0.73/0.91      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.73/0.91         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 0.73/0.91          | (r2_hidden @ (sk_D_2 @ X21 @ X19 @ X20) @ X19)
% 0.73/0.91          | ~ (v1_relat_1 @ X21))),
% 0.73/0.91      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.73/0.91  thf('57', plain,
% 0.73/0.91      ((~ (v1_relat_1 @ sk_D_3)
% 0.73/0.91        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.73/0.91      inference('sup-', [status(thm)], ['55', '56'])).
% 0.73/0.91  thf('58', plain, ((v1_relat_1 @ sk_D_3)),
% 0.73/0.91      inference('sup-', [status(thm)], ['7', '8'])).
% 0.73/0.91  thf('59', plain, ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 0.73/0.91      inference('demod', [status(thm)], ['57', '58'])).
% 0.73/0.91  thf('60', plain,
% 0.73/0.91      (((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E)))),
% 0.73/0.91      inference('demod', [status(thm)], ['54', '59'])).
% 0.73/0.91  thf('61', plain,
% 0.73/0.91      ((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.73/0.91        sk_D_3)),
% 0.73/0.91      inference('demod', [status(thm)], ['44', '45'])).
% 0.73/0.91  thf(t8_funct_1, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i]:
% 0.73/0.91     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.73/0.91       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.73/0.91         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.73/0.91           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.73/0.91  thf('62', plain,
% 0.73/0.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.73/0.91         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 0.73/0.91          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 0.73/0.91          | ~ (v1_funct_1 @ X23)
% 0.73/0.91          | ~ (v1_relat_1 @ X23))),
% 0.73/0.91      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.73/0.91  thf('63', plain,
% 0.73/0.91      ((~ (v1_relat_1 @ sk_D_3)
% 0.73/0.91        | ~ (v1_funct_1 @ sk_D_3)
% 0.73/0.91        | ((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 0.73/0.91      inference('sup-', [status(thm)], ['61', '62'])).
% 0.73/0.91  thf('64', plain, ((v1_relat_1 @ sk_D_3)),
% 0.73/0.91      inference('sup-', [status(thm)], ['7', '8'])).
% 0.73/0.91  thf('65', plain, ((v1_funct_1 @ sk_D_3)),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('66', plain,
% 0.73/0.91      (((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E)))),
% 0.73/0.91      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.73/0.91  thf('67', plain, (((sk_E) != (sk_E))),
% 0.73/0.91      inference('demod', [status(thm)], ['60', '66'])).
% 0.73/0.91  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 0.73/0.91  
% 0.73/0.91  % SZS output end Refutation
% 0.73/0.91  
% 0.73/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
