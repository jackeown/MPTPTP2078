%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2PJ4w58gFZ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:17 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 188 expanded)
%              Number of leaves         :   42 (  74 expanded)
%              Depth                    :   21
%              Number of atoms          :  807 (2127 expanded)
%              Number of equality atoms :   56 ( 143 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
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
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
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
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_B )
      | ( X42
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X42 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('21',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = X0 )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( ( k2_relat_1 @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['31','43'])).

thf('45',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['50','53'])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('56',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('58',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['56','57'])).

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

thf('59',plain,(
    ! [X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X18
       != ( k2_relat_1 @ X16 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( X20
       != ( k1_funct_1 @ X16 @ X21 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('60',plain,(
    ! [X16: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X21 ) @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['16','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['10','70'])).

thf('72',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['45','48'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2PJ4w58gFZ
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:56:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.58/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.82  % Solved by: fo/fo7.sh
% 0.58/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.82  % done 331 iterations in 0.355s
% 0.58/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.82  % SZS output start Refutation
% 0.58/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.82  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.58/0.82  thf(sk_E_type, type, sk_E: $i > $i).
% 0.58/0.82  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.82  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.58/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.58/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.82  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.58/0.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.82  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.58/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.58/0.82  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.82  thf(t16_funct_2, conjecture,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.82       ( ( ![D:$i]:
% 0.58/0.82           ( ~( ( r2_hidden @ D @ B ) & 
% 0.58/0.82                ( ![E:$i]:
% 0.58/0.82                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.58/0.82                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.58/0.82         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.82    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.82        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.82            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.82          ( ( ![D:$i]:
% 0.58/0.82              ( ~( ( r2_hidden @ D @ B ) & 
% 0.58/0.82                   ( ![E:$i]:
% 0.58/0.82                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.58/0.82                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.58/0.82            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.58/0.82    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.58/0.82  thf('0', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(cc2_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.58/0.82  thf('1', plain,
% 0.58/0.82      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.82         ((v5_relat_1 @ X25 @ X27)
% 0.58/0.82          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.82  thf('2', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 0.58/0.82      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.82  thf(d19_relat_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( v1_relat_1 @ B ) =>
% 0.58/0.82       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.58/0.82  thf('3', plain,
% 0.58/0.82      (![X13 : $i, X14 : $i]:
% 0.58/0.82         (~ (v5_relat_1 @ X13 @ X14)
% 0.58/0.82          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.58/0.82          | ~ (v1_relat_1 @ X13))),
% 0.58/0.82      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.58/0.82  thf('4', plain,
% 0.58/0.82      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.82  thf('5', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(cc1_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( v1_relat_1 @ C ) ))).
% 0.58/0.82  thf('6', plain,
% 0.58/0.82      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.58/0.82         ((v1_relat_1 @ X22)
% 0.58/0.82          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.82  thf('7', plain, ((v1_relat_1 @ sk_C_2)),
% 0.58/0.82      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.82  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.58/0.82      inference('demod', [status(thm)], ['4', '7'])).
% 0.58/0.82  thf(d10_xboole_0, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.82  thf('9', plain,
% 0.58/0.82      (![X4 : $i, X6 : $i]:
% 0.58/0.82         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.58/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.82  thf('10', plain,
% 0.58/0.82      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.58/0.82        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['8', '9'])).
% 0.58/0.82  thf(d3_tarski, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.58/0.82  thf('11', plain,
% 0.58/0.82      (![X1 : $i, X3 : $i]:
% 0.58/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.58/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.82  thf('12', plain,
% 0.58/0.82      (![X42 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X42 @ sk_B)
% 0.58/0.82          | ((X42) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X42))))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('13', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r1_tarski @ sk_B @ X0)
% 0.58/0.82          | ((sk_C @ X0 @ sk_B)
% 0.58/0.82              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.82  thf('14', plain,
% 0.58/0.82      (![X1 : $i, X3 : $i]:
% 0.58/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.58/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.82  thf('15', plain,
% 0.58/0.82      (![X42 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X42 @ sk_B) | (r2_hidden @ (sk_E @ X42) @ sk_A))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('16', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r1_tarski @ sk_B @ X0)
% 0.58/0.82          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.82  thf(d1_funct_2, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.82           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.82             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.82         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.82           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.82             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_1, axiom,
% 0.58/0.82    (![B:$i,A:$i]:
% 0.58/0.82     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.82       ( zip_tseitin_0 @ B @ A ) ))).
% 0.58/0.82  thf('17', plain,
% 0.58/0.82      (![X34 : $i, X35 : $i]:
% 0.58/0.82         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.82  thf('18', plain,
% 0.58/0.82      (![X34 : $i, X35 : $i]:
% 0.58/0.82         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.82  thf('19', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.82         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 0.58/0.82      inference('sup+', [status(thm)], ['17', '18'])).
% 0.58/0.82  thf('20', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.58/0.82  thf(zf_stmt_3, axiom,
% 0.58/0.82    (![C:$i,B:$i,A:$i]:
% 0.58/0.82     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.58/0.82       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.58/0.82  thf(zf_stmt_5, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.58/0.82         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.82           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.82             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.82  thf('21', plain,
% 0.58/0.82      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.58/0.82         (~ (zip_tseitin_0 @ X39 @ X40)
% 0.58/0.82          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 0.58/0.82          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.82  thf('22', plain,
% 0.58/0.82      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.58/0.82        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.82  thf('23', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((zip_tseitin_0 @ X1 @ X0)
% 0.58/0.82          | ((sk_B) = (X1))
% 0.58/0.82          | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['19', '22'])).
% 0.58/0.82  thf('24', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('25', plain,
% 0.58/0.82      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.58/0.82         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.58/0.82          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.58/0.82          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.82  thf('26', plain,
% 0.58/0.82      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.58/0.82        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['24', '25'])).
% 0.58/0.82  thf('27', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.82  thf('28', plain,
% 0.58/0.82      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.82         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.58/0.82          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.82  thf('29', plain,
% 0.58/0.82      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['27', '28'])).
% 0.58/0.82  thf('30', plain,
% 0.58/0.82      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.58/0.82        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.58/0.82      inference('demod', [status(thm)], ['26', '29'])).
% 0.58/0.82  thf('31', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (((sk_B) = (X0))
% 0.58/0.82          | (zip_tseitin_0 @ X0 @ X1)
% 0.58/0.82          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['23', '30'])).
% 0.58/0.82  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.58/0.82      inference('demod', [status(thm)], ['4', '7'])).
% 0.58/0.82  thf('33', plain,
% 0.58/0.82      (![X1 : $i, X3 : $i]:
% 0.58/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.58/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.82  thf('34', plain,
% 0.58/0.82      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.58/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.82  thf('35', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.58/0.82      inference('simplify', [status(thm)], ['34'])).
% 0.58/0.82  thf(t3_subset, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.82  thf('36', plain,
% 0.58/0.82      (![X7 : $i, X9 : $i]:
% 0.58/0.82         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.82  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.82  thf(t5_subset, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.58/0.82          ( v1_xboole_0 @ C ) ) ))).
% 0.58/0.82  thf('38', plain,
% 0.58/0.82      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X10 @ X11)
% 0.58/0.82          | ~ (v1_xboole_0 @ X12)
% 0.58/0.82          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t5_subset])).
% 0.58/0.82  thf('39', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['37', '38'])).
% 0.58/0.82  thf('40', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['33', '39'])).
% 0.58/0.82  thf('41', plain,
% 0.58/0.82      (![X4 : $i, X6 : $i]:
% 0.58/0.82         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.58/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.82  thf('42', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['40', '41'])).
% 0.58/0.82  thf('43', plain,
% 0.58/0.82      ((((k2_relat_1 @ sk_C_2) = (sk_B)) | ~ (v1_xboole_0 @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['32', '42'])).
% 0.58/0.82  thf('44', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (~ (v1_xboole_0 @ X0)
% 0.58/0.82          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 0.58/0.82          | (zip_tseitin_0 @ X0 @ X1)
% 0.58/0.82          | ((k2_relat_1 @ sk_C_2) = (sk_B)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['31', '43'])).
% 0.58/0.82  thf('45', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('46', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(redefinition_k2_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.58/0.82  thf('47', plain,
% 0.58/0.82      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.58/0.82         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.58/0.82          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.58/0.82  thf('48', plain,
% 0.58/0.82      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.82  thf('49', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.58/0.82      inference('demod', [status(thm)], ['45', '48'])).
% 0.58/0.82  thf('50', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (~ (v1_xboole_0 @ X0)
% 0.58/0.82          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 0.58/0.82          | (zip_tseitin_0 @ X0 @ X1))),
% 0.58/0.82      inference('simplify_reflect-', [status(thm)], ['44', '49'])).
% 0.58/0.82  thf('51', plain,
% 0.58/0.82      (![X34 : $i, X35 : $i]:
% 0.58/0.82         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.82  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.58/0.82  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.82  thf('53', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.58/0.82      inference('sup+', [status(thm)], ['51', '52'])).
% 0.58/0.82  thf('54', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((zip_tseitin_0 @ X0 @ X1) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.58/0.82      inference('clc', [status(thm)], ['50', '53'])).
% 0.58/0.82  thf('55', plain,
% 0.58/0.82      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.58/0.82        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.82  thf('56', plain,
% 0.58/0.82      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 0.58/0.82        | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.82  thf('57', plain,
% 0.58/0.82      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.58/0.82        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.58/0.82      inference('demod', [status(thm)], ['26', '29'])).
% 0.58/0.82  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.58/0.82      inference('clc', [status(thm)], ['56', '57'])).
% 0.58/0.82  thf(d5_funct_1, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.82       ( ![B:$i]:
% 0.58/0.82         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.58/0.82           ( ![C:$i]:
% 0.58/0.82             ( ( r2_hidden @ C @ B ) <=>
% 0.58/0.82               ( ?[D:$i]:
% 0.58/0.82                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.58/0.82                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.58/0.82  thf('59', plain,
% 0.58/0.82      (![X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.58/0.82         (((X18) != (k2_relat_1 @ X16))
% 0.58/0.82          | (r2_hidden @ X20 @ X18)
% 0.58/0.82          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.58/0.82          | ((X20) != (k1_funct_1 @ X16 @ X21))
% 0.58/0.82          | ~ (v1_funct_1 @ X16)
% 0.58/0.82          | ~ (v1_relat_1 @ X16))),
% 0.58/0.82      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.58/0.82  thf('60', plain,
% 0.58/0.82      (![X16 : $i, X21 : $i]:
% 0.58/0.82         (~ (v1_relat_1 @ X16)
% 0.58/0.82          | ~ (v1_funct_1 @ X16)
% 0.58/0.82          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.58/0.82          | (r2_hidden @ (k1_funct_1 @ X16 @ X21) @ (k2_relat_1 @ X16)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['59'])).
% 0.58/0.82  thf('61', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X0 @ sk_A)
% 0.58/0.82          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.58/0.82          | ~ (v1_funct_1 @ sk_C_2)
% 0.58/0.82          | ~ (v1_relat_1 @ sk_C_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['58', '60'])).
% 0.58/0.82  thf('62', plain, ((v1_funct_1 @ sk_C_2)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('63', plain, ((v1_relat_1 @ sk_C_2)),
% 0.58/0.82      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.82  thf('64', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X0 @ sk_A)
% 0.58/0.82          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.58/0.82      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.58/0.82  thf('65', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r1_tarski @ sk_B @ X0)
% 0.58/0.82          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.58/0.82             (k2_relat_1 @ sk_C_2)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['16', '64'])).
% 0.58/0.82  thf('66', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 0.58/0.82          | (r1_tarski @ sk_B @ X0)
% 0.58/0.82          | (r1_tarski @ sk_B @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['13', '65'])).
% 0.58/0.82  thf('67', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r1_tarski @ sk_B @ X0)
% 0.58/0.82          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['66'])).
% 0.58/0.82  thf('68', plain,
% 0.58/0.82      (![X1 : $i, X3 : $i]:
% 0.58/0.82         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.58/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.82  thf('69', plain,
% 0.58/0.82      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.58/0.82        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['67', '68'])).
% 0.58/0.82  thf('70', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.58/0.82      inference('simplify', [status(thm)], ['69'])).
% 0.58/0.82  thf('71', plain, (((sk_B) = (k2_relat_1 @ sk_C_2))),
% 0.58/0.82      inference('demod', [status(thm)], ['10', '70'])).
% 0.58/0.82  thf('72', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.58/0.82      inference('demod', [status(thm)], ['45', '48'])).
% 0.58/0.82  thf('73', plain, ($false),
% 0.58/0.82      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.58/0.82  
% 0.58/0.82  % SZS output end Refutation
% 0.58/0.82  
% 0.58/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
