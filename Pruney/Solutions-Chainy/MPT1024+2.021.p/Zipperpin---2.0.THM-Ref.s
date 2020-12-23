%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BXNZl8rn6p

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:36 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 161 expanded)
%              Number of leaves         :   42 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  679 (2031 expanded)
%              Number of equality atoms :   34 (  80 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X17: $i,X18: $i] :
      ( ( X17
       != ( k9_relat_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X18 @ X14 @ X15 ) @ X18 @ X14 @ X15 )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k9_relat_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X18 @ X14 @ X15 ) @ X18 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
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

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('16',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_2 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('17',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_1 @ X42 @ X43 )
      | ( zip_tseitin_2 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('20',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_1 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ sk_E_2 @ sk_B ),
    inference('sup-',[status(thm)],['24','31'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('34',plain,(
    ~ ( r1_tarski @ sk_B @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['20','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['17','36','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['14','40'])).

thf('42',plain,(
    ! [X45: $i] :
      ( ~ ( r2_hidden @ X45 @ sk_A )
      | ~ ( r2_hidden @ X45 @ sk_C_1 )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10
        = ( k1_funct_1 @ X8 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('46',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('49',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BXNZl8rn6p
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.70  % Solved by: fo/fo7.sh
% 0.48/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.70  % done 231 iterations in 0.247s
% 0.48/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.70  % SZS output start Refutation
% 0.48/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.70  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.48/0.70  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.48/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.48/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.48/0.70  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.48/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.48/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.48/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.70  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.48/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.48/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.48/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.48/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.70  thf(t115_funct_2, conjecture,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.70       ( ![E:$i]:
% 0.48/0.70         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.48/0.70              ( ![F:$i]:
% 0.48/0.70                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.48/0.70                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.48/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.70        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.70            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.70          ( ![E:$i]:
% 0.48/0.70            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.48/0.70                 ( ![F:$i]:
% 0.48/0.70                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.48/0.70                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.48/0.70    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.48/0.70  thf('0', plain,
% 0.48/0.70      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('1', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(redefinition_k7_relset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.48/0.70  thf('2', plain,
% 0.48/0.70      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.48/0.70          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 0.48/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.48/0.70  thf('3', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.48/0.70           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.70  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.48/0.70      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.70  thf(d12_funct_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.48/0.70       ( ![B:$i,C:$i]:
% 0.48/0.70         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.48/0.70           ( ![D:$i]:
% 0.48/0.70             ( ( r2_hidden @ D @ C ) <=>
% 0.48/0.70               ( ?[E:$i]:
% 0.48/0.70                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.48/0.70                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.48/0.70  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.48/0.70  thf(zf_stmt_2, axiom,
% 0.48/0.70    (![E:$i,D:$i,B:$i,A:$i]:
% 0.48/0.70     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.48/0.70       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.48/0.70         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.48/0.70  thf(zf_stmt_3, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.48/0.70       ( ![B:$i,C:$i]:
% 0.48/0.70         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.48/0.70           ( ![D:$i]:
% 0.48/0.70             ( ( r2_hidden @ D @ C ) <=>
% 0.48/0.70               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.48/0.70  thf('5', plain,
% 0.48/0.70      (![X14 : $i, X15 : $i, X17 : $i, X18 : $i]:
% 0.48/0.70         (((X17) != (k9_relat_1 @ X15 @ X14))
% 0.48/0.70          | (zip_tseitin_0 @ (sk_E_1 @ X18 @ X14 @ X15) @ X18 @ X14 @ X15)
% 0.48/0.70          | ~ (r2_hidden @ X18 @ X17)
% 0.48/0.70          | ~ (v1_funct_1 @ X15)
% 0.48/0.70          | ~ (v1_relat_1 @ X15))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.70  thf('6', plain,
% 0.48/0.70      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X15)
% 0.48/0.70          | ~ (v1_funct_1 @ X15)
% 0.48/0.70          | ~ (r2_hidden @ X18 @ (k9_relat_1 @ X15 @ X14))
% 0.48/0.70          | (zip_tseitin_0 @ (sk_E_1 @ X18 @ X14 @ X15) @ X18 @ X14 @ X15))),
% 0.48/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.48/0.70  thf('7', plain,
% 0.48/0.70      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.48/0.70         sk_C_1 @ sk_D_1)
% 0.48/0.70        | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.70        | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['4', '6'])).
% 0.48/0.70  thf('8', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('9', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(cc1_relset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70       ( v1_relat_1 @ C ) ))).
% 0.48/0.70  thf('10', plain,
% 0.48/0.70      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.48/0.70         ((v1_relat_1 @ X23)
% 0.48/0.70          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.48/0.70  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.48/0.70  thf('12', plain,
% 0.48/0.70      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.48/0.70        sk_C_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.48/0.70  thf('13', plain,
% 0.48/0.70      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.48/0.70         ((r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.48/0.70          | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.70  thf('14', plain,
% 0.48/0.70      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.48/0.70  thf('15', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(d1_funct_2, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.48/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.48/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.48/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.48/0.70  thf(zf_stmt_4, axiom,
% 0.48/0.70    (![C:$i,B:$i,A:$i]:
% 0.48/0.70     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.48/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.48/0.70  thf('16', plain,
% 0.48/0.70      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.48/0.70         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 0.48/0.70          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 0.48/0.70          | ~ (zip_tseitin_2 @ X41 @ X40 @ X39))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.48/0.70  thf('17', plain,
% 0.48/0.70      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.48/0.70        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['15', '16'])).
% 0.48/0.70  thf('18', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.48/0.70  thf(zf_stmt_6, type, zip_tseitin_1 : $i > $i > $o).
% 0.48/0.70  thf(zf_stmt_7, axiom,
% 0.48/0.70    (![B:$i,A:$i]:
% 0.48/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.70       ( zip_tseitin_1 @ B @ A ) ))).
% 0.48/0.70  thf(zf_stmt_8, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.48/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.48/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.48/0.70  thf('19', plain,
% 0.48/0.70      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.48/0.70         (~ (zip_tseitin_1 @ X42 @ X43)
% 0.48/0.70          | (zip_tseitin_2 @ X44 @ X42 @ X43)
% 0.48/0.70          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.48/0.70  thf('20', plain,
% 0.48/0.70      (((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.48/0.70        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.70  thf('21', plain,
% 0.48/0.70      (![X37 : $i, X38 : $i]:
% 0.48/0.70         ((zip_tseitin_1 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.48/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.48/0.70  thf('22', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.48/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.70  thf('23', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.48/0.70      inference('sup+', [status(thm)], ['21', '22'])).
% 0.48/0.70  thf('24', plain,
% 0.48/0.70      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('25', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(dt_k7_relset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.48/0.70  thf('26', plain,
% 0.48/0.70      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.48/0.70          | (m1_subset_1 @ (k7_relset_1 @ X27 @ X28 @ X26 @ X29) @ 
% 0.48/0.70             (k1_zfmisc_1 @ X28)))),
% 0.48/0.70      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.48/0.70  thf('27', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.48/0.70          (k1_zfmisc_1 @ sk_B))),
% 0.48/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.70  thf(t3_subset, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.70  thf('28', plain,
% 0.48/0.70      (![X5 : $i, X6 : $i]:
% 0.48/0.70         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.70  thf('29', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ sk_B)),
% 0.48/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.70  thf(d3_tarski, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.48/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.48/0.70  thf('30', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.48/0.70          | (r2_hidden @ X0 @ X2)
% 0.48/0.70          | ~ (r1_tarski @ X1 @ X2))),
% 0.48/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.70  thf('31', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((r2_hidden @ X1 @ sk_B)
% 0.48/0.70          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.70  thf('32', plain, ((r2_hidden @ sk_E_2 @ sk_B)),
% 0.48/0.70      inference('sup-', [status(thm)], ['24', '31'])).
% 0.48/0.70  thf(t7_ordinal1, axiom,
% 0.48/0.70    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.70  thf('33', plain,
% 0.48/0.70      (![X21 : $i, X22 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 0.48/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.48/0.70  thf('34', plain, (~ (r1_tarski @ sk_B @ sk_E_2)),
% 0.48/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.48/0.70  thf('35', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_B @ X0)),
% 0.48/0.70      inference('sup-', [status(thm)], ['23', '34'])).
% 0.48/0.70  thf('36', plain, ((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)),
% 0.48/0.70      inference('demod', [status(thm)], ['20', '35'])).
% 0.48/0.70  thf('37', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.48/0.70  thf('38', plain,
% 0.48/0.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.48/0.70         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.48/0.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.48/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.48/0.70  thf('39', plain,
% 0.48/0.70      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.70  thf('40', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.48/0.70      inference('demod', [status(thm)], ['17', '36', '39'])).
% 0.48/0.70  thf('41', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_A)),
% 0.48/0.70      inference('demod', [status(thm)], ['14', '40'])).
% 0.48/0.70  thf('42', plain,
% 0.48/0.70      (![X45 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X45 @ sk_A)
% 0.48/0.70          | ~ (r2_hidden @ X45 @ sk_C_1)
% 0.48/0.70          | ((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X45)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('43', plain,
% 0.48/0.70      ((((sk_E_2)
% 0.48/0.70          != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1)))
% 0.48/0.70        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_C_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.48/0.70  thf('44', plain,
% 0.48/0.70      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.48/0.70        sk_C_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.48/0.70  thf('45', plain,
% 0.48/0.70      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.48/0.70         (((X10) = (k1_funct_1 @ X8 @ X9))
% 0.48/0.70          | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.70  thf('46', plain,
% 0.48/0.70      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.48/0.70  thf('47', plain,
% 0.48/0.70      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.48/0.70        sk_C_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.48/0.70  thf('48', plain,
% 0.48/0.70      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.48/0.70         ((r2_hidden @ X9 @ X11) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.70  thf('49', plain,
% 0.48/0.70      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_C_1)),
% 0.48/0.70      inference('sup-', [status(thm)], ['47', '48'])).
% 0.48/0.70  thf('50', plain, (((sk_E_2) != (sk_E_2))),
% 0.48/0.70      inference('demod', [status(thm)], ['43', '46', '49'])).
% 0.48/0.70  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.48/0.70  
% 0.48/0.70  % SZS output end Refutation
% 0.48/0.70  
% 0.48/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
