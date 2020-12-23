%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vGc2enTfQQ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:23 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 159 expanded)
%              Number of leaves         :   41 (  65 expanded)
%              Depth                    :   19
%              Number of atoms          :  694 (1706 expanded)
%              Number of equality atoms :   43 ( 104 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v5_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_B )
      | ( X44
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X44 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('23',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf('26',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('27',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_2 )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_B != sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['24','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['21','41','44'])).

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

thf('46',plain,(
    ! [X21: $i,X23: $i,X25: $i,X26: $i] :
      ( ( X23
       != ( k2_relat_1 @ X21 ) )
      | ( r2_hidden @ X25 @ X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X21 ) )
      | ( X25
       != ( k1_funct_1 @ X21 @ X26 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('47',plain,(
    ! [X21: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X21 @ X26 ) @ ( k2_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['7','8'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['18','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['12','57'])).

thf('59',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['34','37'])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vGc2enTfQQ
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:07:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 306 iterations in 0.222s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.68  thf(sk_E_type, type, sk_E: $i > $i).
% 0.45/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.68  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.68  thf(t16_funct_2, conjecture,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68       ( ( ![D:$i]:
% 0.45/0.68           ( ~( ( r2_hidden @ D @ B ) & 
% 0.45/0.68                ( ![E:$i]:
% 0.45/0.68                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.45/0.68                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.45/0.68         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.68        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.68            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68          ( ( ![D:$i]:
% 0.45/0.68              ( ~( ( r2_hidden @ D @ B ) & 
% 0.45/0.68                   ( ![E:$i]:
% 0.45/0.68                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.45/0.68                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.45/0.68            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.45/0.68  thf('0', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(cc2_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.68         ((v5_relat_1 @ X27 @ X29)
% 0.45/0.68          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.68  thf('2', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 0.45/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.68  thf(d19_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ B ) =>
% 0.45/0.68       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (![X16 : $i, X17 : $i]:
% 0.45/0.68         (~ (v5_relat_1 @ X16 @ X17)
% 0.45/0.68          | (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.45/0.68          | ~ (v1_relat_1 @ X16))),
% 0.45/0.68      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(cc2_relat_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (![X14 : $i, X15 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.45/0.68          | (v1_relat_1 @ X14)
% 0.45/0.68          | ~ (v1_relat_1 @ X15))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 0.45/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.68  thf(fc6_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.68  thf('9', plain, ((v1_relat_1 @ sk_C_2)),
% 0.45/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.68  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.45/0.68      inference('demod', [status(thm)], ['4', '9'])).
% 0.45/0.68  thf(d10_xboole_0, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (![X4 : $i, X6 : $i]:
% 0.45/0.68         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.45/0.68        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.68  thf(d3_tarski, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      (![X1 : $i, X3 : $i]:
% 0.45/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      (![X44 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X44 @ sk_B)
% 0.45/0.68          | ((X44) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X44))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((r1_tarski @ sk_B @ X0)
% 0.45/0.68          | ((sk_C @ X0 @ sk_B)
% 0.45/0.68              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (![X1 : $i, X3 : $i]:
% 0.45/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.68  thf('17', plain,
% 0.45/0.68      (![X44 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X44 @ sk_B) | (r2_hidden @ (sk_E @ X44) @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((r1_tarski @ sk_B @ X0)
% 0.45/0.68          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('19', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(d1_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_1, axiom,
% 0.45/0.68    (![C:$i,B:$i,A:$i]:
% 0.45/0.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.68         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.45/0.68          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.45/0.68          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.45/0.68        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.68  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.68  thf(zf_stmt_4, axiom,
% 0.45/0.68    (![B:$i,A:$i]:
% 0.45/0.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.68       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.68  thf(zf_stmt_5, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.45/0.68         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.45/0.68          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.45/0.68          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.68  thf('24', plain,
% 0.45/0.68      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.45/0.68        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.68  thf('25', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.45/0.68      inference('demod', [status(thm)], ['4', '9'])).
% 0.45/0.68  thf('26', plain,
% 0.45/0.68      (![X36 : $i, X37 : $i]:
% 0.45/0.68         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.45/0.68  thf(t4_subset_1, axiom,
% 0.45/0.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.68  thf('27', plain,
% 0.45/0.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.68  thf(t3_subset, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      (![X8 : $i, X9 : $i]:
% 0.45/0.68         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.68  thf('29', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.68      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.68  thf('30', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.45/0.68      inference('sup+', [status(thm)], ['26', '29'])).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      (![X4 : $i, X6 : $i]:
% 0.45/0.68         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((k2_relat_1 @ sk_C_2) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['25', '32'])).
% 0.45/0.68  thf('34', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.68  thf('36', plain,
% 0.45/0.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 0.45/0.68          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.45/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.68  thf('38', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['34', '37'])).
% 0.45/0.68  thf('39', plain,
% 0.45/0.68      (![X0 : $i]: (((sk_B) != (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['33', '38'])).
% 0.45/0.68  thf('40', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.45/0.68      inference('simplify', [status(thm)], ['39'])).
% 0.45/0.68  thf('41', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)),
% 0.45/0.68      inference('demod', [status(thm)], ['24', '40'])).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.68  thf('43', plain,
% 0.45/0.68      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.68         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.45/0.68          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.68  thf('44', plain,
% 0.45/0.68      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.45/0.68      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.68  thf('45', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.45/0.68      inference('demod', [status(thm)], ['21', '41', '44'])).
% 0.45/0.68  thf(d5_funct_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.68               ( ?[D:$i]:
% 0.45/0.68                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.45/0.68                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('46', plain,
% 0.45/0.68      (![X21 : $i, X23 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         (((X23) != (k2_relat_1 @ X21))
% 0.45/0.68          | (r2_hidden @ X25 @ X23)
% 0.45/0.68          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X21))
% 0.45/0.68          | ((X25) != (k1_funct_1 @ X21 @ X26))
% 0.45/0.68          | ~ (v1_funct_1 @ X21)
% 0.45/0.68          | ~ (v1_relat_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.68  thf('47', plain,
% 0.45/0.68      (![X21 : $i, X26 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ X21)
% 0.45/0.68          | ~ (v1_funct_1 @ X21)
% 0.45/0.68          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X21))
% 0.45/0.68          | (r2_hidden @ (k1_funct_1 @ X21 @ X26) @ (k2_relat_1 @ X21)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.68  thf('48', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.68          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.45/0.68          | ~ (v1_funct_1 @ sk_C_2)
% 0.45/0.68          | ~ (v1_relat_1 @ sk_C_2))),
% 0.45/0.68      inference('sup-', [status(thm)], ['45', '47'])).
% 0.45/0.68  thf('49', plain, ((v1_funct_1 @ sk_C_2)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('50', plain, ((v1_relat_1 @ sk_C_2)),
% 0.45/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.68  thf('51', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.68          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.45/0.68      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.45/0.68  thf('52', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((r1_tarski @ sk_B @ X0)
% 0.45/0.68          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.45/0.68             (k2_relat_1 @ sk_C_2)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['18', '51'])).
% 0.45/0.68  thf('53', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 0.45/0.68          | (r1_tarski @ sk_B @ X0)
% 0.45/0.68          | (r1_tarski @ sk_B @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['15', '52'])).
% 0.45/0.68  thf('54', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((r1_tarski @ sk_B @ X0)
% 0.45/0.68          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.68  thf('55', plain,
% 0.45/0.68      (![X1 : $i, X3 : $i]:
% 0.45/0.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.68  thf('56', plain,
% 0.45/0.68      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.45/0.68        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.68  thf('57', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.45/0.68      inference('simplify', [status(thm)], ['56'])).
% 0.45/0.68  thf('58', plain, (((sk_B) = (k2_relat_1 @ sk_C_2))),
% 0.45/0.68      inference('demod', [status(thm)], ['12', '57'])).
% 0.45/0.68  thf('59', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['34', '37'])).
% 0.45/0.68  thf('60', plain, ($false),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
