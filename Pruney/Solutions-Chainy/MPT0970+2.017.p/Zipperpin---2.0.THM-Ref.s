%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fNoomNr396

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:19 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 271 expanded)
%              Number of leaves         :   41 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          :  796 (3207 expanded)
%              Number of equality atoms :   55 ( 202 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

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

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('8',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['5','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('16',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X35 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( sk_E @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

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

thf('24',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('28',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('47',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B @ ( sk_C @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['16','19'])).

thf('50',plain,
    ( ( k1_xboole_0 != sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('53',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['50','55'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('57',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X11 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('60',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','61'])).

thf('63',plain,(
    r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','20'])).

thf('64',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_B )
      | ( X35
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B )
    = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('68',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','20'])).

thf('70',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['16','19'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fNoomNr396
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:35:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 1.15/1.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.15/1.34  % Solved by: fo/fo7.sh
% 1.15/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.34  % done 1430 iterations in 0.872s
% 1.15/1.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.15/1.34  % SZS output start Refutation
% 1.15/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.34  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.34  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.15/1.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.15/1.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.15/1.34  thf(sk_E_type, type, sk_E: $i > $i).
% 1.15/1.34  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.15/1.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.34  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.15/1.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.15/1.34  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.15/1.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.15/1.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.15/1.34  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.15/1.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.15/1.34  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.15/1.34  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.15/1.34  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.15/1.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.15/1.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.15/1.34  thf(t2_tarski, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 1.15/1.34       ( ( A ) = ( B ) ) ))).
% 1.15/1.34  thf('0', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (((X1) = (X0))
% 1.15/1.34          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 1.15/1.34          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 1.15/1.34      inference('cnf', [status(esa)], [t2_tarski])).
% 1.15/1.34  thf(t16_funct_2, conjecture,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.34       ( ( ![D:$i]:
% 1.15/1.34           ( ~( ( r2_hidden @ D @ B ) & 
% 1.15/1.34                ( ![E:$i]:
% 1.15/1.34                  ( ~( ( r2_hidden @ E @ A ) & 
% 1.15/1.34                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.15/1.34         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 1.15/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.34    (~( ![A:$i,B:$i,C:$i]:
% 1.15/1.34        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.34            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.34          ( ( ![D:$i]:
% 1.15/1.34              ( ~( ( r2_hidden @ D @ B ) & 
% 1.15/1.34                   ( ![E:$i]:
% 1.15/1.34                     ( ~( ( r2_hidden @ E @ A ) & 
% 1.15/1.34                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.15/1.34            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 1.15/1.34    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 1.15/1.34  thf('1', plain,
% 1.15/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(cc2_relset_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.15/1.34  thf('2', plain,
% 1.15/1.34      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.15/1.34         ((v5_relat_1 @ X18 @ X20)
% 1.15/1.34          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.15/1.34      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.15/1.34  thf('3', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 1.15/1.34      inference('sup-', [status(thm)], ['1', '2'])).
% 1.15/1.34  thf(d19_relat_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( v1_relat_1 @ B ) =>
% 1.15/1.34       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.15/1.34  thf('4', plain,
% 1.15/1.34      (![X9 : $i, X10 : $i]:
% 1.15/1.34         (~ (v5_relat_1 @ X9 @ X10)
% 1.15/1.34          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 1.15/1.34          | ~ (v1_relat_1 @ X9))),
% 1.15/1.34      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.15/1.34  thf('5', plain,
% 1.15/1.34      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 1.15/1.34      inference('sup-', [status(thm)], ['3', '4'])).
% 1.15/1.34  thf('6', plain,
% 1.15/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(cc1_relset_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( v1_relat_1 @ C ) ))).
% 1.15/1.34  thf('7', plain,
% 1.15/1.34      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.15/1.34         ((v1_relat_1 @ X15)
% 1.15/1.34          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.15/1.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.15/1.34  thf('8', plain, ((v1_relat_1 @ sk_C_1)),
% 1.15/1.34      inference('sup-', [status(thm)], ['6', '7'])).
% 1.15/1.34  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 1.15/1.34      inference('demod', [status(thm)], ['5', '8'])).
% 1.15/1.34  thf(t3_subset, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.15/1.34  thf('10', plain,
% 1.15/1.34      (![X6 : $i, X8 : $i]:
% 1.15/1.34         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.15/1.34  thf('11', plain,
% 1.15/1.34      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 1.15/1.34      inference('sup-', [status(thm)], ['9', '10'])).
% 1.15/1.34  thf(l3_subset_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.15/1.34       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.15/1.34  thf('12', plain,
% 1.15/1.34      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X3 @ X4)
% 1.15/1.34          | (r2_hidden @ X3 @ X5)
% 1.15/1.34          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 1.15/1.34      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.15/1.34  thf('13', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['11', '12'])).
% 1.15/1.34  thf('14', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ X0) @ X0)
% 1.15/1.34          | ((X0) = (k2_relat_1 @ sk_C_1))
% 1.15/1.34          | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ X0) @ sk_B))),
% 1.15/1.34      inference('sup-', [status(thm)], ['0', '13'])).
% 1.15/1.34  thf('15', plain,
% 1.15/1.34      ((((sk_B) = (k2_relat_1 @ sk_C_1))
% 1.15/1.34        | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 1.15/1.34      inference('eq_fact', [status(thm)], ['14'])).
% 1.15/1.34  thf('16', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('17', plain,
% 1.15/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(redefinition_k2_relset_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.15/1.34  thf('18', plain,
% 1.15/1.34      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.15/1.34         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 1.15/1.34          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.15/1.34      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.15/1.34  thf('19', plain,
% 1.15/1.34      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['17', '18'])).
% 1.15/1.34  thf('20', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 1.15/1.34      inference('demod', [status(thm)], ['16', '19'])).
% 1.15/1.34  thf('21', plain,
% 1.15/1.34      ((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B)),
% 1.15/1.34      inference('simplify_reflect-', [status(thm)], ['15', '20'])).
% 1.15/1.34  thf('22', plain,
% 1.15/1.34      (![X35 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X35 @ sk_B) | (r2_hidden @ (sk_E @ X35) @ sk_A))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('23', plain,
% 1.15/1.34      ((r2_hidden @ (sk_E @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B)) @ sk_A)),
% 1.15/1.34      inference('sup-', [status(thm)], ['21', '22'])).
% 1.15/1.34  thf(d1_funct_2, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.15/1.34           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.15/1.34             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.15/1.34         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.15/1.34           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.15/1.34             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.15/1.34  thf(zf_stmt_1, axiom,
% 1.15/1.34    (![B:$i,A:$i]:
% 1.15/1.34     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.15/1.34       ( zip_tseitin_0 @ B @ A ) ))).
% 1.15/1.34  thf('24', plain,
% 1.15/1.34      (![X27 : $i, X28 : $i]:
% 1.15/1.34         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.15/1.34  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.15/1.34  thf('25', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 1.15/1.34      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.15/1.34  thf('26', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.15/1.34      inference('sup+', [status(thm)], ['24', '25'])).
% 1.15/1.34  thf('27', plain,
% 1.15/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.15/1.34  thf(zf_stmt_3, axiom,
% 1.15/1.34    (![C:$i,B:$i,A:$i]:
% 1.15/1.34     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.15/1.34       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.15/1.34  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.15/1.34  thf(zf_stmt_5, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.15/1.34         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.15/1.34           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.15/1.34             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.15/1.34  thf('28', plain,
% 1.15/1.34      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.15/1.34         (~ (zip_tseitin_0 @ X32 @ X33)
% 1.15/1.34          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 1.15/1.34          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.15/1.34  thf('29', plain,
% 1.15/1.34      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.15/1.34        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.15/1.34      inference('sup-', [status(thm)], ['27', '28'])).
% 1.15/1.34  thf('30', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 1.15/1.34      inference('sup-', [status(thm)], ['26', '29'])).
% 1.15/1.34  thf('31', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('32', plain,
% 1.15/1.34      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.15/1.34         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 1.15/1.34          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 1.15/1.34          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.15/1.34  thf('33', plain,
% 1.15/1.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.15/1.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['31', '32'])).
% 1.15/1.34  thf('34', plain,
% 1.15/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(redefinition_k1_relset_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.15/1.34  thf('35', plain,
% 1.15/1.34      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.15/1.34         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 1.15/1.34          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.15/1.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.15/1.34  thf('36', plain,
% 1.15/1.34      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['34', '35'])).
% 1.15/1.34  thf('37', plain,
% 1.15/1.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.15/1.34        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.15/1.34      inference('demod', [status(thm)], ['33', '36'])).
% 1.15/1.34  thf('38', plain,
% 1.15/1.34      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['30', '37'])).
% 1.15/1.34  thf('39', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 1.15/1.34      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.15/1.34  thf('40', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (((X1) = (X0))
% 1.15/1.34          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 1.15/1.34          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 1.15/1.34      inference('cnf', [status(esa)], [t2_tarski])).
% 1.15/1.34  thf(t7_ordinal1, axiom,
% 1.15/1.34    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.15/1.34  thf('41', plain,
% 1.15/1.34      (![X13 : $i, X14 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 1.15/1.34      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.15/1.34  thf('42', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 1.15/1.34          | ((X1) = (X0))
% 1.15/1.34          | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ X1)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['40', '41'])).
% 1.15/1.34  thf('43', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['39', '42'])).
% 1.15/1.34  thf('44', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['11', '12'])).
% 1.15/1.34  thf('45', plain,
% 1.15/1.34      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 1.15/1.34        | (r2_hidden @ (sk_C @ k1_xboole_0 @ (k2_relat_1 @ sk_C_1)) @ sk_B))),
% 1.15/1.34      inference('sup-', [status(thm)], ['43', '44'])).
% 1.15/1.34  thf('46', plain,
% 1.15/1.34      (![X13 : $i, X14 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 1.15/1.34      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.15/1.34  thf('47', plain,
% 1.15/1.34      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 1.15/1.34        | ~ (r1_tarski @ sk_B @ (sk_C @ k1_xboole_0 @ (k2_relat_1 @ sk_C_1))))),
% 1.15/1.34      inference('sup-', [status(thm)], ['45', '46'])).
% 1.15/1.34  thf('48', plain,
% 1.15/1.34      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 1.15/1.34        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['38', '47'])).
% 1.15/1.34  thf('49', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 1.15/1.34      inference('demod', [status(thm)], ['16', '19'])).
% 1.15/1.34  thf('50', plain,
% 1.15/1.34      ((((k1_xboole_0) != (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['48', '49'])).
% 1.15/1.34  thf('51', plain,
% 1.15/1.34      (![X27 : $i, X28 : $i]:
% 1.15/1.34         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.15/1.34  thf('52', plain,
% 1.15/1.34      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.15/1.34        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.15/1.34      inference('sup-', [status(thm)], ['27', '28'])).
% 1.15/1.34  thf('53', plain,
% 1.15/1.34      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 1.15/1.34      inference('sup-', [status(thm)], ['51', '52'])).
% 1.15/1.34  thf('54', plain,
% 1.15/1.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.15/1.34        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.15/1.34      inference('demod', [status(thm)], ['33', '36'])).
% 1.15/1.34  thf('55', plain,
% 1.15/1.34      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['53', '54'])).
% 1.15/1.34  thf('56', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.15/1.34      inference('clc', [status(thm)], ['50', '55'])).
% 1.15/1.34  thf(t12_funct_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.15/1.34       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.15/1.34         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 1.15/1.34  thf('57', plain,
% 1.15/1.34      (![X11 : $i, X12 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 1.15/1.34          | (r2_hidden @ (k1_funct_1 @ X12 @ X11) @ (k2_relat_1 @ X12))
% 1.15/1.34          | ~ (v1_funct_1 @ X12)
% 1.15/1.34          | ~ (v1_relat_1 @ X12))),
% 1.15/1.34      inference('cnf', [status(esa)], [t12_funct_1])).
% 1.15/1.34  thf('58', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X0 @ sk_A)
% 1.15/1.34          | ~ (v1_relat_1 @ sk_C_1)
% 1.15/1.34          | ~ (v1_funct_1 @ sk_C_1)
% 1.15/1.34          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['56', '57'])).
% 1.15/1.34  thf('59', plain, ((v1_relat_1 @ sk_C_1)),
% 1.15/1.34      inference('sup-', [status(thm)], ['6', '7'])).
% 1.15/1.34  thf('60', plain, ((v1_funct_1 @ sk_C_1)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('61', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X0 @ sk_A)
% 1.15/1.34          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 1.15/1.34      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.15/1.34  thf('62', plain,
% 1.15/1.34      ((r2_hidden @ 
% 1.15/1.34        (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B))) @ 
% 1.15/1.34        (k2_relat_1 @ sk_C_1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['23', '61'])).
% 1.15/1.34  thf('63', plain,
% 1.15/1.34      ((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B)),
% 1.15/1.34      inference('simplify_reflect-', [status(thm)], ['15', '20'])).
% 1.15/1.34  thf('64', plain,
% 1.15/1.34      (![X35 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X35 @ sk_B)
% 1.15/1.34          | ((X35) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X35))))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('65', plain,
% 1.15/1.34      (((sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B)
% 1.15/1.34         = (k1_funct_1 @ sk_C_1 @ 
% 1.15/1.34            (sk_E @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B))))),
% 1.15/1.34      inference('sup-', [status(thm)], ['63', '64'])).
% 1.15/1.34  thf('66', plain,
% 1.15/1.34      ((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ 
% 1.15/1.34        (k2_relat_1 @ sk_C_1))),
% 1.15/1.34      inference('demod', [status(thm)], ['62', '65'])).
% 1.15/1.34  thf('67', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (((X1) = (X0))
% 1.15/1.34          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 1.15/1.34          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 1.15/1.34      inference('cnf', [status(esa)], [t2_tarski])).
% 1.15/1.34  thf('68', plain,
% 1.15/1.34      ((~ (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B)
% 1.15/1.34        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['66', '67'])).
% 1.15/1.34  thf('69', plain,
% 1.15/1.34      ((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B)),
% 1.15/1.34      inference('simplify_reflect-', [status(thm)], ['15', '20'])).
% 1.15/1.34  thf('70', plain, (((sk_B) = (k2_relat_1 @ sk_C_1))),
% 1.15/1.34      inference('demod', [status(thm)], ['68', '69'])).
% 1.15/1.34  thf('71', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 1.15/1.34      inference('demod', [status(thm)], ['16', '19'])).
% 1.15/1.34  thf('72', plain, ($false),
% 1.15/1.34      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 1.15/1.34  
% 1.15/1.34  % SZS output end Refutation
% 1.15/1.34  
% 1.15/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
