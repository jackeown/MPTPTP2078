%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nrehWaur4u

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:17 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 160 expanded)
%              Number of leaves         :   42 (  66 expanded)
%              Depth                    :   19
%              Number of atoms          :  697 (1715 expanded)
%              Number of equality atoms :   46 ( 108 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_B )
      | ( X44
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X44 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('21',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t25_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X34: $i,X35: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t25_relset_1])).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('33',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['28','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['37','42'])).

thf('44',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['22','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','44','47'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X19 @ X18 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','59'])).

thf('61',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['38','41'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nrehWaur4u
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:11:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.84/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.06  % Solved by: fo/fo7.sh
% 0.84/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.06  % done 651 iterations in 0.582s
% 0.84/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.06  % SZS output start Refutation
% 0.84/1.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.84/1.06  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.84/1.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.06  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.84/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.84/1.06  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.84/1.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.84/1.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.84/1.06  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.84/1.06  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.84/1.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.84/1.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.84/1.06  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.84/1.06  thf(sk_E_type, type, sk_E: $i > $i).
% 0.84/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.06  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.84/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.84/1.06  thf(t16_funct_2, conjecture,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.06       ( ( ![D:$i]:
% 0.84/1.06           ( ~( ( r2_hidden @ D @ B ) & 
% 0.84/1.06                ( ![E:$i]:
% 0.84/1.06                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.84/1.06                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.84/1.06         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.84/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.06    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.06        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.06            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.06          ( ( ![D:$i]:
% 0.84/1.06              ( ~( ( r2_hidden @ D @ B ) & 
% 0.84/1.06                   ( ![E:$i]:
% 0.84/1.06                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.84/1.06                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.84/1.06            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.84/1.06    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.84/1.06  thf('0', plain,
% 0.84/1.06      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(cc2_relset_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.06       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.84/1.06  thf('1', plain,
% 0.84/1.06      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.84/1.06         ((v5_relat_1 @ X25 @ X27)
% 0.84/1.06          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.84/1.06      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.84/1.06  thf('2', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.84/1.06      inference('sup-', [status(thm)], ['0', '1'])).
% 0.84/1.06  thf(d19_relat_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( v1_relat_1 @ B ) =>
% 0.84/1.06       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.84/1.06  thf('3', plain,
% 0.84/1.06      (![X10 : $i, X11 : $i]:
% 0.84/1.06         (~ (v5_relat_1 @ X10 @ X11)
% 0.84/1.06          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.84/1.06          | ~ (v1_relat_1 @ X10))),
% 0.84/1.06      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.84/1.06  thf('4', plain,
% 0.84/1.06      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.84/1.06      inference('sup-', [status(thm)], ['2', '3'])).
% 0.84/1.06  thf('5', plain,
% 0.84/1.06      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(cc1_relset_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.06       ( v1_relat_1 @ C ) ))).
% 0.84/1.06  thf('6', plain,
% 0.84/1.06      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.84/1.06         ((v1_relat_1 @ X22)
% 0.84/1.06          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.84/1.06      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.84/1.06  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 0.84/1.06      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.06  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.84/1.06      inference('demod', [status(thm)], ['4', '7'])).
% 0.84/1.06  thf(d10_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.84/1.06  thf('9', plain,
% 0.84/1.06      (![X4 : $i, X6 : $i]:
% 0.84/1.06         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.84/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.06  thf('10', plain,
% 0.84/1.06      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.84/1.06        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['8', '9'])).
% 0.84/1.06  thf(d3_tarski, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( r1_tarski @ A @ B ) <=>
% 0.84/1.06       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.84/1.06  thf('11', plain,
% 0.84/1.06      (![X1 : $i, X3 : $i]:
% 0.84/1.06         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.06  thf('12', plain,
% 0.84/1.06      (![X44 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X44 @ sk_B)
% 0.84/1.06          | ((X44) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X44))))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('13', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r1_tarski @ sk_B @ X0)
% 0.84/1.06          | ((sk_C @ X0 @ sk_B)
% 0.84/1.06              = (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['11', '12'])).
% 0.84/1.06  thf('14', plain,
% 0.84/1.06      (![X1 : $i, X3 : $i]:
% 0.84/1.06         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.06  thf('15', plain,
% 0.84/1.06      (![X44 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X44 @ sk_B) | (r2_hidden @ (sk_E @ X44) @ sk_A))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('16', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r1_tarski @ sk_B @ X0)
% 0.84/1.06          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['14', '15'])).
% 0.84/1.06  thf('17', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(d1_funct_2, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.06       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.84/1.06           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.84/1.06             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.84/1.06         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.84/1.06           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.84/1.06             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.84/1.06  thf(zf_stmt_1, axiom,
% 0.84/1.06    (![C:$i,B:$i,A:$i]:
% 0.84/1.06     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.84/1.06       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.84/1.06  thf('18', plain,
% 0.84/1.06      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.84/1.06         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.84/1.06          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.84/1.06          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.84/1.06  thf('19', plain,
% 0.84/1.06      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.84/1.06        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.84/1.06  thf('20', plain,
% 0.84/1.06      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.84/1.06  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.84/1.06  thf(zf_stmt_4, axiom,
% 0.84/1.06    (![B:$i,A:$i]:
% 0.84/1.06     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.84/1.06       ( zip_tseitin_0 @ B @ A ) ))).
% 0.84/1.06  thf(zf_stmt_5, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.06       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.84/1.06         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.84/1.06           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.84/1.06             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.84/1.06  thf('21', plain,
% 0.84/1.06      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.84/1.06         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.84/1.06          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.84/1.06          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.84/1.06  thf('22', plain,
% 0.84/1.06      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.84/1.06        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.84/1.06  thf('23', plain,
% 0.84/1.06      (![X36 : $i, X37 : $i]:
% 0.84/1.06         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.84/1.06  thf(t25_relset_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.84/1.06  thf('24', plain,
% 0.84/1.06      (![X34 : $i, X35 : $i]:
% 0.84/1.06         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t25_relset_1])).
% 0.84/1.06  thf('25', plain,
% 0.84/1.06      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.84/1.06         ((v5_relat_1 @ X25 @ X27)
% 0.84/1.06          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.84/1.06      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.84/1.06  thf('26', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.84/1.06      inference('sup-', [status(thm)], ['24', '25'])).
% 0.84/1.06  thf('27', plain,
% 0.84/1.06      (![X10 : $i, X11 : $i]:
% 0.84/1.06         (~ (v5_relat_1 @ X10 @ X11)
% 0.84/1.06          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.84/1.06          | ~ (v1_relat_1 @ X10))),
% 0.84/1.06      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.84/1.06  thf('28', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (v1_relat_1 @ k1_xboole_0)
% 0.84/1.06          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['26', '27'])).
% 0.84/1.06  thf(t113_zfmisc_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.84/1.06       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.84/1.06  thf('29', plain,
% 0.84/1.06      (![X8 : $i, X9 : $i]:
% 0.84/1.06         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.84/1.06  thf('30', plain,
% 0.84/1.06      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.84/1.06      inference('simplify', [status(thm)], ['29'])).
% 0.84/1.06  thf(fc6_relat_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.84/1.06  thf('31', plain,
% 0.84/1.06      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.84/1.06      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.84/1.06  thf('32', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.84/1.06      inference('sup+', [status(thm)], ['30', '31'])).
% 0.84/1.06  thf(t60_relat_1, axiom,
% 0.84/1.06    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.84/1.06     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.84/1.06  thf('33', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.84/1.06      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.84/1.06  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.84/1.06      inference('demod', [status(thm)], ['28', '32', '33'])).
% 0.84/1.06  thf('35', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.84/1.06      inference('sup+', [status(thm)], ['23', '34'])).
% 0.84/1.06  thf('36', plain,
% 0.84/1.06      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.84/1.06        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['8', '9'])).
% 0.84/1.06  thf('37', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((zip_tseitin_0 @ sk_B @ X0) | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.06  thf('38', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('39', plain,
% 0.84/1.06      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(redefinition_k2_relset_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.06       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.84/1.06  thf('40', plain,
% 0.84/1.06      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.84/1.06         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.84/1.06          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.84/1.06      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.84/1.06  thf('41', plain,
% 0.84/1.06      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.84/1.06      inference('sup-', [status(thm)], ['39', '40'])).
% 0.84/1.06  thf('42', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.84/1.06      inference('demod', [status(thm)], ['38', '41'])).
% 0.84/1.06  thf('43', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.84/1.06      inference('simplify_reflect-', [status(thm)], ['37', '42'])).
% 0.84/1.06  thf('44', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.84/1.06      inference('demod', [status(thm)], ['22', '43'])).
% 0.84/1.06  thf('45', plain,
% 0.84/1.06      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(redefinition_k1_relset_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.06       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.84/1.06  thf('46', plain,
% 0.84/1.06      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.84/1.06         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.84/1.06          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.84/1.06      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.84/1.06  thf('47', plain,
% 0.84/1.06      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.84/1.06      inference('sup-', [status(thm)], ['45', '46'])).
% 0.84/1.06  thf('48', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.84/1.06      inference('demod', [status(thm)], ['19', '44', '47'])).
% 0.84/1.06  thf(t12_funct_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.06       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.84/1.06         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.84/1.06  thf('49', plain,
% 0.84/1.06      (![X18 : $i, X19 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.84/1.06          | (r2_hidden @ (k1_funct_1 @ X19 @ X18) @ (k2_relat_1 @ X19))
% 0.84/1.06          | ~ (v1_funct_1 @ X19)
% 0.84/1.06          | ~ (v1_relat_1 @ X19))),
% 0.84/1.06      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.84/1.06  thf('50', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X0 @ sk_A)
% 0.84/1.06          | ~ (v1_relat_1 @ sk_C_1)
% 0.84/1.06          | ~ (v1_funct_1 @ sk_C_1)
% 0.84/1.06          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['48', '49'])).
% 0.84/1.06  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 0.84/1.06      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.06  thf('52', plain, ((v1_funct_1 @ sk_C_1)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('53', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X0 @ sk_A)
% 0.84/1.06          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.84/1.06      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.84/1.06  thf('54', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r1_tarski @ sk_B @ X0)
% 0.84/1.06          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.84/1.06             (k2_relat_1 @ sk_C_1)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['16', '53'])).
% 0.84/1.06  thf('55', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_1))
% 0.84/1.06          | (r1_tarski @ sk_B @ X0)
% 0.84/1.06          | (r1_tarski @ sk_B @ X0))),
% 0.84/1.06      inference('sup+', [status(thm)], ['13', '54'])).
% 0.84/1.06  thf('56', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r1_tarski @ sk_B @ X0)
% 0.84/1.06          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_1)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['55'])).
% 0.84/1.06  thf('57', plain,
% 0.84/1.06      (![X1 : $i, X3 : $i]:
% 0.84/1.06         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.06  thf('58', plain,
% 0.84/1.06      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.84/1.06        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['56', '57'])).
% 0.84/1.06  thf('59', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))),
% 0.84/1.06      inference('simplify', [status(thm)], ['58'])).
% 0.84/1.06  thf('60', plain, (((sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.84/1.06      inference('demod', [status(thm)], ['10', '59'])).
% 0.84/1.06  thf('61', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.84/1.06      inference('demod', [status(thm)], ['38', '41'])).
% 0.84/1.06  thf('62', plain, ($false),
% 0.84/1.06      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.84/1.06  
% 0.84/1.06  % SZS output end Refutation
% 0.84/1.06  
% 0.84/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
