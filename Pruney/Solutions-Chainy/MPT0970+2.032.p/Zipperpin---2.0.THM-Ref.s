%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lr4JCCckAC

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:21 EST 2020

% Result     : Theorem 3.33s
% Output     : Refutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  144 (2227 expanded)
%              Number of leaves         :   37 ( 640 expanded)
%              Depth                    :   28
%              Number of atoms          : 1032 (34423 expanded)
%              Number of equality atoms :  114 (2622 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t16_funct_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
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
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
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

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('5',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( sk_D_4 @ X26 @ X24 ) @ X24 )
      | ( ( k2_relset_1 @ X25 @ X24 @ X26 )
        = X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('13',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B )
    | ( r2_hidden @ ( sk_D_4 @ sk_C_2 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
    | ( r2_hidden @ ( sk_D_4 @ sk_C_2 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('18',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ ( sk_D_4 @ sk_C_2 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ X37 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D_4 @ sk_C_2 @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('24',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

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

thf('29',plain,(
    ! [X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( X13
       != ( k1_funct_1 @ X9 @ X14 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('30',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E_1 @ ( sk_D_4 @ sk_C_2 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_D_4 @ sk_C_2 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','18'])).

thf('39',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( X37
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E_1 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_D_4 @ sk_C_2 @ sk_B )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_E_1 @ ( sk_D_4 @ sk_C_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_D_4 @ sk_C_2 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('43',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D_4 @ sk_C_2 @ sk_B ) @ sk_C_2 ) @ ( sk_D_4 @ sk_C_2 @ sk_B ) ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_D_4 @ X26 @ X24 ) ) @ X26 )
      | ( ( k2_relset_1 @ X25 @ X24 @ X26 )
        = X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','46'])).

thf('48',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','47'])).

thf('49',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('50',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['6','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 != k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('60',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('63',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('64',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('66',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('70',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['51','68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('72',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('75',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('77',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['76','78'])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('84',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( sk_A != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( ( k2_relat_1 @ sk_C_2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( sk_A != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k2_relat_1 @ sk_C_2 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_2 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != sk_B )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('96',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['75','96'])).

thf('98',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['70','97'])).

thf('99',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('100',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('102',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lr4JCCckAC
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.33/3.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.33/3.54  % Solved by: fo/fo7.sh
% 3.33/3.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.33/3.54  % done 1847 iterations in 3.094s
% 3.33/3.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.33/3.54  % SZS output start Refutation
% 3.33/3.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.33/3.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.33/3.54  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.33/3.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.33/3.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.33/3.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.33/3.54  thf(sk_A_type, type, sk_A: $i).
% 3.33/3.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.33/3.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.33/3.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.33/3.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 3.33/3.54  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i).
% 3.33/3.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.33/3.54  thf(sk_B_type, type, sk_B: $i).
% 3.33/3.54  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 3.33/3.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.33/3.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.33/3.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.33/3.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.33/3.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.33/3.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.33/3.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.33/3.54  thf(t16_funct_2, conjecture,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.33/3.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.33/3.54       ( ( ![D:$i]:
% 3.33/3.54           ( ~( ( r2_hidden @ D @ B ) & 
% 3.33/3.54                ( ![E:$i]:
% 3.33/3.54                  ( ~( ( r2_hidden @ E @ A ) & 
% 3.33/3.54                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 3.33/3.54         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 3.33/3.54  thf(zf_stmt_0, negated_conjecture,
% 3.33/3.54    (~( ![A:$i,B:$i,C:$i]:
% 3.33/3.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.33/3.54            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.33/3.54          ( ( ![D:$i]:
% 3.33/3.54              ( ~( ( r2_hidden @ D @ B ) & 
% 3.33/3.54                   ( ![E:$i]:
% 3.33/3.54                     ( ~( ( r2_hidden @ E @ A ) & 
% 3.33/3.54                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 3.33/3.54            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 3.33/3.54    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 3.33/3.54  thf('0', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf(d1_funct_2, axiom,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.33/3.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.33/3.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.33/3.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.33/3.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.33/3.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.33/3.54  thf(zf_stmt_1, axiom,
% 3.33/3.54    (![C:$i,B:$i,A:$i]:
% 3.33/3.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.33/3.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.33/3.54  thf('1', plain,
% 3.33/3.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.33/3.54         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 3.33/3.54          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 3.33/3.54          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.33/3.54  thf('2', plain,
% 3.33/3.54      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.33/3.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['0', '1'])).
% 3.33/3.54  thf('3', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf(redefinition_k1_relset_1, axiom,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.33/3.54  thf('4', plain,
% 3.33/3.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.33/3.54         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 3.33/3.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.33/3.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.33/3.54  thf('5', plain,
% 3.33/3.54      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 3.33/3.54      inference('sup-', [status(thm)], ['3', '4'])).
% 3.33/3.54  thf('6', plain,
% 3.33/3.54      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.33/3.54        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.33/3.54      inference('demod', [status(thm)], ['2', '5'])).
% 3.33/3.54  thf('7', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf(redefinition_k2_relset_1, axiom,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.33/3.54  thf('8', plain,
% 3.33/3.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.33/3.54         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 3.33/3.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.33/3.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.33/3.54  thf('9', plain,
% 3.33/3.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 3.33/3.54      inference('sup-', [status(thm)], ['7', '8'])).
% 3.33/3.54  thf('10', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('11', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf(t23_relset_1, axiom,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.54       ( ( ![D:$i]:
% 3.33/3.54           ( ~( ( r2_hidden @ D @ B ) & 
% 3.33/3.54                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 3.33/3.54         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 3.33/3.54  thf('12', plain,
% 3.33/3.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.33/3.54         ((r2_hidden @ (sk_D_4 @ X26 @ X24) @ X24)
% 3.33/3.54          | ((k2_relset_1 @ X25 @ X24 @ X26) = (X24))
% 3.33/3.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 3.33/3.54      inference('cnf', [status(esa)], [t23_relset_1])).
% 3.33/3.54  thf('13', plain,
% 3.33/3.54      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))
% 3.33/3.54        | (r2_hidden @ (sk_D_4 @ sk_C_2 @ sk_B) @ sk_B))),
% 3.33/3.54      inference('sup-', [status(thm)], ['11', '12'])).
% 3.33/3.54  thf('14', plain,
% 3.33/3.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 3.33/3.54      inference('sup-', [status(thm)], ['7', '8'])).
% 3.33/3.54  thf('15', plain,
% 3.33/3.54      ((((k2_relat_1 @ sk_C_2) = (sk_B))
% 3.33/3.54        | (r2_hidden @ (sk_D_4 @ sk_C_2 @ sk_B) @ sk_B))),
% 3.33/3.54      inference('demod', [status(thm)], ['13', '14'])).
% 3.33/3.54  thf('16', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('17', plain,
% 3.33/3.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 3.33/3.54      inference('sup-', [status(thm)], ['7', '8'])).
% 3.33/3.54  thf('18', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 3.33/3.54      inference('demod', [status(thm)], ['16', '17'])).
% 3.33/3.54  thf('19', plain, ((r2_hidden @ (sk_D_4 @ sk_C_2 @ sk_B) @ sk_B)),
% 3.33/3.54      inference('simplify_reflect-', [status(thm)], ['15', '18'])).
% 3.33/3.54  thf('20', plain,
% 3.33/3.54      (![X37 : $i]:
% 3.33/3.54         (~ (r2_hidden @ X37 @ sk_B) | (r2_hidden @ (sk_E_1 @ X37) @ sk_A))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('21', plain, ((r2_hidden @ (sk_E_1 @ (sk_D_4 @ sk_C_2 @ sk_B)) @ sk_A)),
% 3.33/3.54      inference('sup-', [status(thm)], ['19', '20'])).
% 3.33/3.54  thf(zf_stmt_2, axiom,
% 3.33/3.54    (![B:$i,A:$i]:
% 3.33/3.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.33/3.54       ( zip_tseitin_0 @ B @ A ) ))).
% 3.33/3.54  thf('22', plain,
% 3.33/3.54      (![X29 : $i, X30 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.33/3.54  thf('23', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.33/3.54  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.33/3.54  thf(zf_stmt_5, axiom,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.33/3.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.33/3.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.33/3.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.33/3.54  thf('24', plain,
% 3.33/3.54      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.33/3.54         (~ (zip_tseitin_0 @ X34 @ X35)
% 3.33/3.54          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 3.33/3.54          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.33/3.54  thf('25', plain,
% 3.33/3.54      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.33/3.54        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.33/3.54      inference('sup-', [status(thm)], ['23', '24'])).
% 3.33/3.54  thf('26', plain,
% 3.33/3.54      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 3.33/3.54      inference('sup-', [status(thm)], ['22', '25'])).
% 3.33/3.54  thf('27', plain,
% 3.33/3.54      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.33/3.54        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.33/3.54      inference('demod', [status(thm)], ['2', '5'])).
% 3.33/3.54  thf('28', plain,
% 3.33/3.54      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['26', '27'])).
% 3.33/3.54  thf(d5_funct_1, axiom,
% 3.33/3.54    (![A:$i]:
% 3.33/3.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.33/3.54       ( ![B:$i]:
% 3.33/3.54         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.33/3.54           ( ![C:$i]:
% 3.33/3.54             ( ( r2_hidden @ C @ B ) <=>
% 3.33/3.54               ( ?[D:$i]:
% 3.33/3.54                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 3.33/3.54                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 3.33/3.54  thf('29', plain,
% 3.33/3.54      (![X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 3.33/3.54         (((X11) != (k2_relat_1 @ X9))
% 3.33/3.54          | (r2_hidden @ X13 @ X11)
% 3.33/3.54          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 3.33/3.54          | ((X13) != (k1_funct_1 @ X9 @ X14))
% 3.33/3.54          | ~ (v1_funct_1 @ X9)
% 3.33/3.54          | ~ (v1_relat_1 @ X9))),
% 3.33/3.54      inference('cnf', [status(esa)], [d5_funct_1])).
% 3.33/3.54  thf('30', plain,
% 3.33/3.54      (![X9 : $i, X14 : $i]:
% 3.33/3.54         (~ (v1_relat_1 @ X9)
% 3.33/3.54          | ~ (v1_funct_1 @ X9)
% 3.33/3.54          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 3.33/3.54          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 3.33/3.54      inference('simplify', [status(thm)], ['29'])).
% 3.33/3.54  thf('31', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (r2_hidden @ X0 @ sk_A)
% 3.33/3.54          | ((sk_B) = (k1_xboole_0))
% 3.33/3.54          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 3.33/3.54          | ~ (v1_funct_1 @ sk_C_2)
% 3.33/3.54          | ~ (v1_relat_1 @ sk_C_2))),
% 3.33/3.54      inference('sup-', [status(thm)], ['28', '30'])).
% 3.33/3.54  thf('32', plain, ((v1_funct_1 @ sk_C_2)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('33', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf(cc1_relset_1, axiom,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.54       ( v1_relat_1 @ C ) ))).
% 3.33/3.54  thf('34', plain,
% 3.33/3.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.33/3.54         ((v1_relat_1 @ X15)
% 3.33/3.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.33/3.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.33/3.54  thf('35', plain, ((v1_relat_1 @ sk_C_2)),
% 3.33/3.54      inference('sup-', [status(thm)], ['33', '34'])).
% 3.33/3.54  thf('36', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (r2_hidden @ X0 @ sk_A)
% 3.33/3.54          | ((sk_B) = (k1_xboole_0))
% 3.33/3.54          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 3.33/3.54      inference('demod', [status(thm)], ['31', '32', '35'])).
% 3.33/3.54  thf('37', plain,
% 3.33/3.54      (((r2_hidden @ 
% 3.33/3.54         (k1_funct_1 @ sk_C_2 @ (sk_E_1 @ (sk_D_4 @ sk_C_2 @ sk_B))) @ 
% 3.33/3.54         (k2_relat_1 @ sk_C_2))
% 3.33/3.54        | ((sk_B) = (k1_xboole_0)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['21', '36'])).
% 3.33/3.54  thf('38', plain, ((r2_hidden @ (sk_D_4 @ sk_C_2 @ sk_B) @ sk_B)),
% 3.33/3.54      inference('simplify_reflect-', [status(thm)], ['15', '18'])).
% 3.33/3.54  thf('39', plain,
% 3.33/3.54      (![X37 : $i]:
% 3.33/3.54         (~ (r2_hidden @ X37 @ sk_B)
% 3.33/3.54          | ((X37) = (k1_funct_1 @ sk_C_2 @ (sk_E_1 @ X37))))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('40', plain,
% 3.33/3.54      (((sk_D_4 @ sk_C_2 @ sk_B)
% 3.33/3.54         = (k1_funct_1 @ sk_C_2 @ (sk_E_1 @ (sk_D_4 @ sk_C_2 @ sk_B))))),
% 3.33/3.54      inference('sup-', [status(thm)], ['38', '39'])).
% 3.33/3.54  thf('41', plain,
% 3.33/3.54      (((r2_hidden @ (sk_D_4 @ sk_C_2 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 3.33/3.54        | ((sk_B) = (k1_xboole_0)))),
% 3.33/3.54      inference('demod', [status(thm)], ['37', '40'])).
% 3.33/3.54  thf(d5_relat_1, axiom,
% 3.33/3.54    (![A:$i,B:$i]:
% 3.33/3.54     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.33/3.54       ( ![C:$i]:
% 3.33/3.54         ( ( r2_hidden @ C @ B ) <=>
% 3.33/3.54           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 3.33/3.54  thf('42', plain,
% 3.33/3.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.33/3.54         (~ (r2_hidden @ X4 @ X3)
% 3.33/3.54          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 3.33/3.54          | ((X3) != (k2_relat_1 @ X2)))),
% 3.33/3.54      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.33/3.54  thf('43', plain,
% 3.33/3.54      (![X2 : $i, X4 : $i]:
% 3.33/3.54         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 3.33/3.54          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 3.33/3.54      inference('simplify', [status(thm)], ['42'])).
% 3.33/3.54  thf('44', plain,
% 3.33/3.54      ((((sk_B) = (k1_xboole_0))
% 3.33/3.54        | (r2_hidden @ 
% 3.33/3.54           (k4_tarski @ (sk_D_1 @ (sk_D_4 @ sk_C_2 @ sk_B) @ sk_C_2) @ 
% 3.33/3.54            (sk_D_4 @ sk_C_2 @ sk_B)) @ 
% 3.33/3.54           sk_C_2))),
% 3.33/3.54      inference('sup-', [status(thm)], ['41', '43'])).
% 3.33/3.54  thf('45', plain,
% 3.33/3.54      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 3.33/3.54         (~ (r2_hidden @ (k4_tarski @ X28 @ (sk_D_4 @ X26 @ X24)) @ X26)
% 3.33/3.54          | ((k2_relset_1 @ X25 @ X24 @ X26) = (X24))
% 3.33/3.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 3.33/3.54      inference('cnf', [status(esa)], [t23_relset_1])).
% 3.33/3.54  thf('46', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (((sk_B) = (k1_xboole_0))
% 3.33/3.54          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 3.33/3.54          | ((k2_relset_1 @ X0 @ sk_B @ sk_C_2) = (sk_B)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['44', '45'])).
% 3.33/3.54  thf('47', plain,
% 3.33/3.54      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))
% 3.33/3.54        | ((sk_B) = (k1_xboole_0)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['10', '46'])).
% 3.33/3.54  thf('48', plain,
% 3.33/3.54      ((((k2_relat_1 @ sk_C_2) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 3.33/3.54      inference('sup+', [status(thm)], ['9', '47'])).
% 3.33/3.54  thf('49', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 3.33/3.54      inference('demod', [status(thm)], ['16', '17'])).
% 3.33/3.54  thf('50', plain, (((sk_B) = (k1_xboole_0))),
% 3.33/3.54      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 3.33/3.54  thf('51', plain,
% 3.33/3.54      ((~ (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A)
% 3.33/3.54        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.33/3.54      inference('demod', [status(thm)], ['6', '50'])).
% 3.33/3.54  thf('52', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('53', plain, (((sk_B) = (k1_xboole_0))),
% 3.33/3.54      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 3.33/3.54  thf('54', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C_2 @ 
% 3.33/3.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 3.33/3.54      inference('demod', [status(thm)], ['52', '53'])).
% 3.33/3.54  thf('55', plain,
% 3.33/3.54      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.33/3.54         (((X34) != (k1_xboole_0))
% 3.33/3.54          | ((X35) = (k1_xboole_0))
% 3.33/3.54          | ((X36) = (k1_xboole_0))
% 3.33/3.54          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 3.33/3.54          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.33/3.54  thf('56', plain,
% 3.33/3.54      (![X35 : $i, X36 : $i]:
% 3.33/3.54         (~ (m1_subset_1 @ X36 @ 
% 3.33/3.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ k1_xboole_0)))
% 3.33/3.54          | ~ (v1_funct_2 @ X36 @ X35 @ k1_xboole_0)
% 3.33/3.54          | ((X36) = (k1_xboole_0))
% 3.33/3.54          | ((X35) = (k1_xboole_0)))),
% 3.33/3.54      inference('simplify', [status(thm)], ['55'])).
% 3.33/3.54  thf('57', plain,
% 3.33/3.54      ((((sk_A) = (k1_xboole_0))
% 3.33/3.54        | ((sk_C_2) = (k1_xboole_0))
% 3.33/3.54        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0))),
% 3.33/3.54      inference('sup-', [status(thm)], ['54', '56'])).
% 3.33/3.54  thf('58', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('59', plain, (((sk_B) = (k1_xboole_0))),
% 3.33/3.54      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 3.33/3.54  thf('60', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0)),
% 3.33/3.54      inference('demod', [status(thm)], ['58', '59'])).
% 3.33/3.54  thf('61', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 3.33/3.54      inference('demod', [status(thm)], ['57', '60'])).
% 3.33/3.54  thf('62', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 3.33/3.54      inference('demod', [status(thm)], ['16', '17'])).
% 3.33/3.54  thf('63', plain, (((sk_B) = (k1_xboole_0))),
% 3.33/3.54      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 3.33/3.54  thf('64', plain, (((k2_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 3.33/3.54      inference('demod', [status(thm)], ['62', '63'])).
% 3.33/3.54  thf('65', plain,
% 3.33/3.54      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 3.33/3.54        | ((sk_A) = (k1_xboole_0)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['61', '64'])).
% 3.33/3.54  thf(t60_relat_1, axiom,
% 3.33/3.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 3.33/3.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.33/3.54  thf('66', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.33/3.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.33/3.54  thf('67', plain,
% 3.33/3.54      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 3.33/3.54      inference('demod', [status(thm)], ['65', '66'])).
% 3.33/3.54  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 3.33/3.54      inference('simplify', [status(thm)], ['67'])).
% 3.33/3.54  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 3.33/3.54      inference('simplify', [status(thm)], ['67'])).
% 3.33/3.54  thf('70', plain,
% 3.33/3.54      ((~ (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 3.33/3.54        | ((k1_xboole_0) = (k1_relat_1 @ sk_C_2)))),
% 3.33/3.54      inference('demod', [status(thm)], ['51', '68', '69'])).
% 3.33/3.54  thf('71', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C_2 @ 
% 3.33/3.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 3.33/3.54      inference('demod', [status(thm)], ['52', '53'])).
% 3.33/3.54  thf('72', plain, (((sk_A) = (k1_xboole_0))),
% 3.33/3.54      inference('simplify', [status(thm)], ['67'])).
% 3.33/3.54  thf('73', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C_2 @ 
% 3.33/3.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.33/3.54      inference('demod', [status(thm)], ['71', '72'])).
% 3.33/3.54  thf('74', plain,
% 3.33/3.54      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.33/3.54         (~ (zip_tseitin_0 @ X34 @ X35)
% 3.33/3.54          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 3.33/3.54          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.33/3.54  thf('75', plain,
% 3.33/3.54      (((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 3.33/3.54        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.33/3.54      inference('sup-', [status(thm)], ['73', '74'])).
% 3.33/3.54  thf('76', plain,
% 3.33/3.54      (![X29 : $i, X30 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.33/3.54  thf('77', plain,
% 3.33/3.54      (![X29 : $i, X30 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.33/3.54  thf('78', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 3.33/3.54      inference('simplify', [status(thm)], ['77'])).
% 3.33/3.54  thf('79', plain,
% 3.33/3.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 3.33/3.54      inference('sup+', [status(thm)], ['76', '78'])).
% 3.33/3.54  thf('80', plain,
% 3.33/3.54      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.33/3.54        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.33/3.54      inference('sup-', [status(thm)], ['23', '24'])).
% 3.33/3.54  thf('81', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ sk_A @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 3.33/3.54      inference('sup-', [status(thm)], ['79', '80'])).
% 3.33/3.54  thf('82', plain,
% 3.33/3.54      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.33/3.54        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.33/3.54      inference('demod', [status(thm)], ['2', '5'])).
% 3.33/3.54  thf('83', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['81', '82'])).
% 3.33/3.54  thf(t65_relat_1, axiom,
% 3.33/3.54    (![A:$i]:
% 3.33/3.54     ( ( v1_relat_1 @ A ) =>
% 3.33/3.54       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 3.33/3.54         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 3.33/3.54  thf('84', plain,
% 3.33/3.54      (![X7 : $i]:
% 3.33/3.54         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 3.33/3.54          | ((k2_relat_1 @ X7) = (k1_xboole_0))
% 3.33/3.54          | ~ (v1_relat_1 @ X7))),
% 3.33/3.54      inference('cnf', [status(esa)], [t65_relat_1])).
% 3.33/3.54  thf('85', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (((sk_A) != (k1_xboole_0))
% 3.33/3.54          | (zip_tseitin_0 @ sk_A @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ sk_C_2)
% 3.33/3.54          | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['83', '84'])).
% 3.33/3.54  thf('86', plain, ((v1_relat_1 @ sk_C_2)),
% 3.33/3.54      inference('sup-', [status(thm)], ['33', '34'])).
% 3.33/3.54  thf('87', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (((sk_A) != (k1_xboole_0))
% 3.33/3.54          | (zip_tseitin_0 @ sk_A @ X0)
% 3.33/3.54          | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 3.33/3.54      inference('demod', [status(thm)], ['85', '86'])).
% 3.33/3.54  thf('88', plain,
% 3.33/3.54      (![X29 : $i, X30 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.33/3.54  thf('89', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (((k2_relat_1 @ sk_C_2) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_A @ X0))),
% 3.33/3.54      inference('clc', [status(thm)], ['87', '88'])).
% 3.33/3.54  thf('90', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 3.33/3.54      inference('demod', [status(thm)], ['16', '17'])).
% 3.33/3.54  thf('91', plain,
% 3.33/3.54      (![X0 : $i]: (((k1_xboole_0) != (sk_B)) | (zip_tseitin_0 @ sk_A @ X0))),
% 3.33/3.54      inference('sup-', [status(thm)], ['89', '90'])).
% 3.33/3.54  thf('92', plain, (((sk_B) = (k1_xboole_0))),
% 3.33/3.54      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 3.33/3.54  thf('93', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (((k1_xboole_0) != (k1_xboole_0)) | (zip_tseitin_0 @ sk_A @ X0))),
% 3.33/3.54      inference('demod', [status(thm)], ['91', '92'])).
% 3.33/3.54  thf('94', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 3.33/3.54      inference('simplify', [status(thm)], ['93'])).
% 3.33/3.54  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 3.33/3.54      inference('simplify', [status(thm)], ['67'])).
% 3.33/3.54  thf('96', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 3.33/3.54      inference('demod', [status(thm)], ['94', '95'])).
% 3.33/3.54  thf('97', plain, ((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)),
% 3.33/3.54      inference('demod', [status(thm)], ['75', '96'])).
% 3.33/3.54  thf('98', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C_2))),
% 3.33/3.54      inference('demod', [status(thm)], ['70', '97'])).
% 3.33/3.54  thf('99', plain,
% 3.33/3.54      (![X7 : $i]:
% 3.33/3.54         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 3.33/3.54          | ((k2_relat_1 @ X7) = (k1_xboole_0))
% 3.33/3.54          | ~ (v1_relat_1 @ X7))),
% 3.33/3.54      inference('cnf', [status(esa)], [t65_relat_1])).
% 3.33/3.54  thf('100', plain,
% 3.33/3.54      ((((k1_xboole_0) != (k1_xboole_0))
% 3.33/3.54        | ~ (v1_relat_1 @ sk_C_2)
% 3.33/3.54        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['98', '99'])).
% 3.33/3.54  thf('101', plain, ((v1_relat_1 @ sk_C_2)),
% 3.33/3.54      inference('sup-', [status(thm)], ['33', '34'])).
% 3.33/3.54  thf('102', plain,
% 3.33/3.54      ((((k1_xboole_0) != (k1_xboole_0))
% 3.33/3.54        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 3.33/3.54      inference('demod', [status(thm)], ['100', '101'])).
% 3.33/3.54  thf('103', plain, (((k2_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 3.33/3.54      inference('simplify', [status(thm)], ['102'])).
% 3.33/3.54  thf('104', plain, (((k2_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 3.33/3.54      inference('demod', [status(thm)], ['62', '63'])).
% 3.33/3.54  thf('105', plain, ($false),
% 3.33/3.54      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 3.33/3.54  
% 3.33/3.54  % SZS output end Refutation
% 3.33/3.54  
% 3.33/3.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
