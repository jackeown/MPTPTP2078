%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kbmDbGqjif

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:09 EST 2020

% Result     : Theorem 8.95s
% Output     : Refutation 8.95s
% Verified   : 
% Statistics : Number of formulae       :  279 (2703 expanded)
%              Number of leaves         :   45 ( 828 expanded)
%              Depth                    :   37
%              Number of atoms          : 1853 (25589 expanded)
%              Number of equality atoms :  169 (2026 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X22: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X34 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X25 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','17'])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','18','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

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

thf(zf_stmt_0,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('36',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,(
    ! [X35: $i] :
      ( zip_tseitin_0 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['38','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','57'])).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['59'])).

thf('63',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_D ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('66',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['64','67'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X34 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','72'])).

thf('74',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('75',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('79',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('82',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('83',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('85',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('88',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('91',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_D
      = ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( sk_D
        = ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( sk_D
        = ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('98',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('105',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['104'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_2 ) )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('109',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['38','55'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('112',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('113',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['104'])).

thf('114',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('115',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('118',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('120',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','120'])).

thf('122',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('123',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['104'])).

thf('125',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['59'])).

thf('126',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','127'])).

thf('129',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf('130',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('131',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['104'])).

thf('132',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('133',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['129','134'])).

thf('136',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['59'])).

thf('137',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['104'])).

thf('138',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['63','128','135','136','137'])).

thf('139',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['109','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_2 )
      | ( zip_tseitin_0 @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['100','139'])).

thf('141',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('142',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_2 @ X0 ) ),
    inference(clc,[status(thm)],['140','143'])).

thf('145',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['83','144'])).

thf('146',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['80','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('148',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('151',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['73','146','151'])).

thf('153',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('154',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['59'])).

thf('156',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['63','154','155'])).

thf('157',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['60','156'])).

thf('158',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('160',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('163',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('164',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('168',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['161','168'])).

thf('170',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('171',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['158','171'])).

thf('173',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('174',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('175',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('177',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('179',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['64','67'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('181',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('182',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['180','183'])).

thf('185',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['179','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['178','185'])).

thf('187',plain,(
    ! [X25: $i] :
      ( ( ( k2_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X25 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['149','150'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['177','191'])).

thf('193',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['104'])).

thf('194',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['63','128','135','136','137'])).

thf('195',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['192','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('200',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 != k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ( X42 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('201',plain,(
    ! [X41: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('203',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('204',plain,(
    ! [X41: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['199','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['198','210'])).

thf('212',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(condensation,[status(thm)],['211'])).

thf('213',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('214',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['73','146','151'])).

thf('215',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('216',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['73','146','151'])).

thf('218',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('219',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['80','145'])).

thf('221',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['60','156'])).

thf('226',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['216','226'])).

thf('228',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['213','227'])).

thf('229',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('230',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['212','228','229'])).

thf('231',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('232',plain,(
    $false ),
    inference(demod,[status(thm)],['172','230','231'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kbmDbGqjif
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:01:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 8.95/9.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.95/9.20  % Solved by: fo/fo7.sh
% 8.95/9.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.95/9.20  % done 8307 iterations in 8.734s
% 8.95/9.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.95/9.20  % SZS output start Refutation
% 8.95/9.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.95/9.20  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 8.95/9.20  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 8.95/9.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.95/9.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.95/9.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.95/9.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.95/9.20  thf(sk_A_type, type, sk_A: $i).
% 8.95/9.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.95/9.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.95/9.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.95/9.20  thf(sk_C_1_type, type, sk_C_1: $i).
% 8.95/9.20  thf(sk_B_2_type, type, sk_B_2: $i).
% 8.95/9.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.95/9.20  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 8.95/9.20  thf(sk_B_type, type, sk_B: $i > $i).
% 8.95/9.20  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 8.95/9.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.95/9.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.95/9.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.95/9.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.95/9.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 8.95/9.20  thf(sk_D_type, type, sk_D: $i).
% 8.95/9.20  thf(t7_xboole_0, axiom,
% 8.95/9.20    (![A:$i]:
% 8.95/9.20     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 8.95/9.20          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 8.95/9.20  thf('0', plain,
% 8.95/9.20      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 8.95/9.20      inference('cnf', [status(esa)], [t7_xboole_0])).
% 8.95/9.20  thf(d1_xboole_0, axiom,
% 8.95/9.20    (![A:$i]:
% 8.95/9.20     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 8.95/9.20  thf('1', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 8.95/9.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 8.95/9.20  thf('2', plain,
% 8.95/9.20      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['0', '1'])).
% 8.95/9.20  thf('3', plain,
% 8.95/9.20      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['0', '1'])).
% 8.95/9.20  thf(d3_tarski, axiom,
% 8.95/9.20    (![A:$i,B:$i]:
% 8.95/9.20     ( ( r1_tarski @ A @ B ) <=>
% 8.95/9.20       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 8.95/9.20  thf('4', plain,
% 8.95/9.20      (![X4 : $i, X6 : $i]:
% 8.95/9.20         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 8.95/9.20      inference('cnf', [status(esa)], [d3_tarski])).
% 8.95/9.20  thf('5', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 8.95/9.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 8.95/9.20  thf('6', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['4', '5'])).
% 8.95/9.20  thf('7', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['4', '5'])).
% 8.95/9.20  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 8.95/9.20  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.95/9.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.95/9.20  thf(fc10_relat_1, axiom,
% 8.95/9.20    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 8.95/9.20  thf('9', plain,
% 8.95/9.20      (![X22 : $i]:
% 8.95/9.20         ((v1_xboole_0 @ (k1_relat_1 @ X22)) | ~ (v1_xboole_0 @ X22))),
% 8.95/9.20      inference('cnf', [status(esa)], [fc10_relat_1])).
% 8.95/9.20  thf('10', plain,
% 8.95/9.20      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['0', '1'])).
% 8.95/9.20  thf('11', plain,
% 8.95/9.20      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['9', '10'])).
% 8.95/9.20  thf('12', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['8', '11'])).
% 8.95/9.20  thf(t11_relset_1, axiom,
% 8.95/9.20    (![A:$i,B:$i,C:$i]:
% 8.95/9.20     ( ( v1_relat_1 @ C ) =>
% 8.95/9.20       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 8.95/9.20           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 8.95/9.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 8.95/9.20  thf('13', plain,
% 8.95/9.20      (![X32 : $i, X33 : $i, X34 : $i]:
% 8.95/9.20         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 8.95/9.20          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 8.95/9.20          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 8.95/9.20          | ~ (v1_relat_1 @ X32))),
% 8.95/9.20      inference('cnf', [status(esa)], [t11_relset_1])).
% 8.95/9.20  thf('14', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 8.95/9.20          | ~ (v1_relat_1 @ k1_xboole_0)
% 8.95/9.20          | (m1_subset_1 @ k1_xboole_0 @ 
% 8.95/9.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 8.95/9.20          | ~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X1))),
% 8.95/9.20      inference('sup-', [status(thm)], ['12', '13'])).
% 8.95/9.20  thf(t113_zfmisc_1, axiom,
% 8.95/9.20    (![A:$i,B:$i]:
% 8.95/9.20     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 8.95/9.20       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 8.95/9.20  thf('15', plain,
% 8.95/9.20      (![X12 : $i, X13 : $i]:
% 8.95/9.20         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 8.95/9.20          | ((X12) != (k1_xboole_0)))),
% 8.95/9.20      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 8.95/9.20  thf('16', plain,
% 8.95/9.20      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 8.95/9.20      inference('simplify', [status(thm)], ['15'])).
% 8.95/9.20  thf(fc6_relat_1, axiom,
% 8.95/9.20    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.95/9.20  thf('17', plain,
% 8.95/9.20      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 8.95/9.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.95/9.20  thf('18', plain, ((v1_relat_1 @ k1_xboole_0)),
% 8.95/9.20      inference('sup+', [status(thm)], ['16', '17'])).
% 8.95/9.20  thf('19', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['8', '11'])).
% 8.95/9.20  thf(t65_relat_1, axiom,
% 8.95/9.20    (![A:$i]:
% 8.95/9.20     ( ( v1_relat_1 @ A ) =>
% 8.95/9.20       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 8.95/9.20         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 8.95/9.20  thf('20', plain,
% 8.95/9.20      (![X25 : $i]:
% 8.95/9.20         (((k1_relat_1 @ X25) != (k1_xboole_0))
% 8.95/9.20          | ((k2_relat_1 @ X25) = (k1_xboole_0))
% 8.95/9.20          | ~ (v1_relat_1 @ X25))),
% 8.95/9.20      inference('cnf', [status(esa)], [t65_relat_1])).
% 8.95/9.20  thf('21', plain,
% 8.95/9.20      ((((k1_xboole_0) != (k1_xboole_0))
% 8.95/9.20        | ~ (v1_relat_1 @ k1_xboole_0)
% 8.95/9.20        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['19', '20'])).
% 8.95/9.20  thf('22', plain, ((v1_relat_1 @ k1_xboole_0)),
% 8.95/9.20      inference('sup+', [status(thm)], ['16', '17'])).
% 8.95/9.20  thf('23', plain,
% 8.95/9.20      ((((k1_xboole_0) != (k1_xboole_0))
% 8.95/9.20        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 8.95/9.20      inference('demod', [status(thm)], ['21', '22'])).
% 8.95/9.20  thf('24', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.95/9.20      inference('simplify', [status(thm)], ['23'])).
% 8.95/9.20  thf('25', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 8.95/9.20          | (m1_subset_1 @ k1_xboole_0 @ 
% 8.95/9.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 8.95/9.20          | ~ (r1_tarski @ k1_xboole_0 @ X1))),
% 8.95/9.20      inference('demod', [status(thm)], ['14', '18', '24'])).
% 8.95/9.20  thf('26', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (~ (v1_xboole_0 @ k1_xboole_0)
% 8.95/9.20          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 8.95/9.20          | (m1_subset_1 @ k1_xboole_0 @ 
% 8.95/9.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['7', '25'])).
% 8.95/9.20  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.95/9.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.95/9.20  thf('28', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (~ (r1_tarski @ k1_xboole_0 @ X1)
% 8.95/9.20          | (m1_subset_1 @ k1_xboole_0 @ 
% 8.95/9.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 8.95/9.20      inference('demod', [status(thm)], ['26', '27'])).
% 8.95/9.20  thf('29', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (~ (v1_xboole_0 @ k1_xboole_0)
% 8.95/9.20          | (m1_subset_1 @ k1_xboole_0 @ 
% 8.95/9.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['6', '28'])).
% 8.95/9.20  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.95/9.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.95/9.20  thf('31', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 8.95/9.20      inference('demod', [status(thm)], ['29', '30'])).
% 8.95/9.20  thf(redefinition_k1_relset_1, axiom,
% 8.95/9.20    (![A:$i,B:$i,C:$i]:
% 8.95/9.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.95/9.20       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 8.95/9.20  thf('32', plain,
% 8.95/9.20      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.95/9.20         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 8.95/9.20          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 8.95/9.20      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 8.95/9.20  thf('33', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['31', '32'])).
% 8.95/9.20  thf('34', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['8', '11'])).
% 8.95/9.20  thf('35', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 8.95/9.20      inference('demod', [status(thm)], ['33', '34'])).
% 8.95/9.20  thf(d1_funct_2, axiom,
% 8.95/9.20    (![A:$i,B:$i,C:$i]:
% 8.95/9.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.95/9.20       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 8.95/9.20           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 8.95/9.20             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 8.95/9.20         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 8.95/9.20           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 8.95/9.20             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 8.95/9.20  thf(zf_stmt_0, axiom,
% 8.95/9.20    (![C:$i,B:$i,A:$i]:
% 8.95/9.20     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 8.95/9.20       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 8.95/9.20  thf('36', plain,
% 8.95/9.20      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.95/9.20         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 8.95/9.20          | (v1_funct_2 @ X39 @ X37 @ X38)
% 8.95/9.20          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.95/9.20  thf('37', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (((X1) != (k1_xboole_0))
% 8.95/9.20          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 8.95/9.20          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['35', '36'])).
% 8.95/9.20  thf('38', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 8.95/9.20          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 8.95/9.20      inference('simplify', [status(thm)], ['37'])).
% 8.95/9.20  thf(zf_stmt_1, axiom,
% 8.95/9.20    (![B:$i,A:$i]:
% 8.95/9.20     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 8.95/9.20       ( zip_tseitin_0 @ B @ A ) ))).
% 8.95/9.20  thf('39', plain,
% 8.95/9.20      (![X35 : $i, X36 : $i]:
% 8.95/9.20         ((zip_tseitin_0 @ X35 @ X36) | ((X36) != (k1_xboole_0)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.95/9.20  thf('40', plain, (![X35 : $i]: (zip_tseitin_0 @ X35 @ k1_xboole_0)),
% 8.95/9.20      inference('simplify', [status(thm)], ['39'])).
% 8.95/9.20  thf('41', plain,
% 8.95/9.20      (![X4 : $i, X6 : $i]:
% 8.95/9.20         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 8.95/9.20      inference('cnf', [status(esa)], [d3_tarski])).
% 8.95/9.20  thf('42', plain,
% 8.95/9.20      (![X12 : $i, X13 : $i]:
% 8.95/9.20         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 8.95/9.20          | ((X13) != (k1_xboole_0)))),
% 8.95/9.20      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 8.95/9.20  thf('43', plain,
% 8.95/9.20      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 8.95/9.20      inference('simplify', [status(thm)], ['42'])).
% 8.95/9.20  thf('44', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 8.95/9.20      inference('demod', [status(thm)], ['29', '30'])).
% 8.95/9.20  thf(t5_subset, axiom,
% 8.95/9.20    (![A:$i,B:$i,C:$i]:
% 8.95/9.20     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 8.95/9.20          ( v1_xboole_0 @ C ) ) ))).
% 8.95/9.20  thf('45', plain,
% 8.95/9.20      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.95/9.20         (~ (r2_hidden @ X17 @ X18)
% 8.95/9.20          | ~ (v1_xboole_0 @ X19)
% 8.95/9.20          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 8.95/9.20      inference('cnf', [status(esa)], [t5_subset])).
% 8.95/9.20  thf('46', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.95/9.20         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 8.95/9.20          | ~ (r2_hidden @ X2 @ k1_xboole_0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['44', '45'])).
% 8.95/9.20  thf('47', plain,
% 8.95/9.20      (![X1 : $i]:
% 8.95/9.20         (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['43', '46'])).
% 8.95/9.20  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.95/9.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.95/9.20  thf('49', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 8.95/9.20      inference('demod', [status(thm)], ['47', '48'])).
% 8.95/9.20  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 8.95/9.20      inference('sup-', [status(thm)], ['41', '49'])).
% 8.95/9.20  thf(t3_subset, axiom,
% 8.95/9.20    (![A:$i,B:$i]:
% 8.95/9.20     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.95/9.20  thf('51', plain,
% 8.95/9.20      (![X14 : $i, X16 : $i]:
% 8.95/9.20         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 8.95/9.20      inference('cnf', [status(esa)], [t3_subset])).
% 8.95/9.20  thf('52', plain,
% 8.95/9.20      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['50', '51'])).
% 8.95/9.20  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 8.95/9.20  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 8.95/9.20  thf(zf_stmt_4, axiom,
% 8.95/9.20    (![A:$i,B:$i,C:$i]:
% 8.95/9.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.95/9.20       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 8.95/9.20         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 8.95/9.20           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 8.95/9.20             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 8.95/9.20  thf('53', plain,
% 8.95/9.20      (![X40 : $i, X41 : $i, X42 : $i]:
% 8.95/9.20         (~ (zip_tseitin_0 @ X40 @ X41)
% 8.95/9.20          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 8.95/9.20          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_4])).
% 8.95/9.20  thf('54', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 8.95/9.20      inference('sup-', [status(thm)], ['52', '53'])).
% 8.95/9.20  thf('55', plain,
% 8.95/9.20      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 8.95/9.20      inference('sup-', [status(thm)], ['40', '54'])).
% 8.95/9.20  thf('56', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 8.95/9.20      inference('demod', [status(thm)], ['38', '55'])).
% 8.95/9.20  thf('57', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup+', [status(thm)], ['3', '56'])).
% 8.95/9.20  thf('58', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.95/9.20         ((v1_funct_2 @ X2 @ X0 @ X1)
% 8.95/9.20          | ~ (v1_xboole_0 @ X0)
% 8.95/9.20          | ~ (v1_xboole_0 @ X2))),
% 8.95/9.20      inference('sup+', [status(thm)], ['2', '57'])).
% 8.95/9.20  thf(t8_funct_2, conjecture,
% 8.95/9.20    (![A:$i,B:$i,C:$i,D:$i]:
% 8.95/9.20     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 8.95/9.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.95/9.20       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 8.95/9.20         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 8.95/9.20           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 8.95/9.20             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 8.95/9.20  thf(zf_stmt_5, negated_conjecture,
% 8.95/9.20    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 8.95/9.20        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 8.95/9.20            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.95/9.20          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 8.95/9.20            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 8.95/9.20              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 8.95/9.20                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 8.95/9.20    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 8.95/9.20  thf('59', plain,
% 8.95/9.20      ((~ (v1_funct_1 @ sk_D)
% 8.95/9.20        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 8.95/9.20        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.95/9.20  thf('60', plain,
% 8.95/9.20      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 8.95/9.20         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 8.95/9.20      inference('split', [status(esa)], ['59'])).
% 8.95/9.20  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.95/9.20  thf('62', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 8.95/9.20      inference('split', [status(esa)], ['59'])).
% 8.95/9.20  thf('63', plain, (((v1_funct_1 @ sk_D))),
% 8.95/9.20      inference('sup-', [status(thm)], ['61', '62'])).
% 8.95/9.20  thf('64', plain,
% 8.95/9.20      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_D) @ sk_C_1)),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.95/9.20  thf('65', plain,
% 8.95/9.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.95/9.20  thf(redefinition_k2_relset_1, axiom,
% 8.95/9.20    (![A:$i,B:$i,C:$i]:
% 8.95/9.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.95/9.20       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 8.95/9.20  thf('66', plain,
% 8.95/9.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 8.95/9.20         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 8.95/9.20          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 8.95/9.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 8.95/9.20  thf('67', plain,
% 8.95/9.20      (((k2_relset_1 @ sk_A @ sk_B_2 @ sk_D) = (k2_relat_1 @ sk_D))),
% 8.95/9.20      inference('sup-', [status(thm)], ['65', '66'])).
% 8.95/9.20  thf('68', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 8.95/9.20      inference('demod', [status(thm)], ['64', '67'])).
% 8.95/9.20  thf(d10_xboole_0, axiom,
% 8.95/9.20    (![A:$i,B:$i]:
% 8.95/9.20     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.95/9.20  thf('69', plain,
% 8.95/9.20      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 8.95/9.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.95/9.20  thf('70', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 8.95/9.20      inference('simplify', [status(thm)], ['69'])).
% 8.95/9.20  thf('71', plain,
% 8.95/9.20      (![X32 : $i, X33 : $i, X34 : $i]:
% 8.95/9.20         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 8.95/9.20          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 8.95/9.20          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 8.95/9.20          | ~ (v1_relat_1 @ X32))),
% 8.95/9.20      inference('cnf', [status(esa)], [t11_relset_1])).
% 8.95/9.20  thf('72', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (~ (v1_relat_1 @ X0)
% 8.95/9.20          | (m1_subset_1 @ X0 @ 
% 8.95/9.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 8.95/9.20          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 8.95/9.20      inference('sup-', [status(thm)], ['70', '71'])).
% 8.95/9.20  thf('73', plain,
% 8.95/9.20      (((m1_subset_1 @ sk_D @ 
% 8.95/9.20         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1)))
% 8.95/9.20        | ~ (v1_relat_1 @ sk_D))),
% 8.95/9.20      inference('sup-', [status(thm)], ['68', '72'])).
% 8.95/9.20  thf('74', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.95/9.20  thf('75', plain,
% 8.95/9.20      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.95/9.20         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 8.95/9.20          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 8.95/9.20          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.95/9.20  thf('76', plain,
% 8.95/9.20      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 8.95/9.20        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_D)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['74', '75'])).
% 8.95/9.20  thf('77', plain,
% 8.95/9.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.95/9.20  thf('78', plain,
% 8.95/9.20      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.95/9.20         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 8.95/9.20          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 8.95/9.20      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 8.95/9.20  thf('79', plain,
% 8.95/9.20      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_D) = (k1_relat_1 @ sk_D))),
% 8.95/9.20      inference('sup-', [status(thm)], ['77', '78'])).
% 8.95/9.20  thf('80', plain,
% 8.95/9.20      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 8.95/9.20        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 8.95/9.20      inference('demod', [status(thm)], ['76', '79'])).
% 8.95/9.20  thf('81', plain,
% 8.95/9.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.95/9.20  thf('82', plain,
% 8.95/9.20      (![X40 : $i, X41 : $i, X42 : $i]:
% 8.95/9.20         (~ (zip_tseitin_0 @ X40 @ X41)
% 8.95/9.20          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 8.95/9.20          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_4])).
% 8.95/9.20  thf('83', plain,
% 8.95/9.20      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 8.95/9.20        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 8.95/9.20      inference('sup-', [status(thm)], ['81', '82'])).
% 8.95/9.20  thf('84', plain,
% 8.95/9.20      (![X35 : $i, X36 : $i]:
% 8.95/9.20         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.95/9.20  thf('85', plain,
% 8.95/9.20      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 8.95/9.20      inference('simplify', [status(thm)], ['42'])).
% 8.95/9.20  thf('86', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.95/9.20         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 8.95/9.20      inference('sup+', [status(thm)], ['84', '85'])).
% 8.95/9.20  thf('87', plain,
% 8.95/9.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.95/9.20  thf('88', plain,
% 8.95/9.20      (![X14 : $i, X15 : $i]:
% 8.95/9.20         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 8.95/9.20      inference('cnf', [status(esa)], [t3_subset])).
% 8.95/9.20  thf('89', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_2))),
% 8.95/9.20      inference('sup-', [status(thm)], ['87', '88'])).
% 8.95/9.20  thf('90', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['4', '5'])).
% 8.95/9.20  thf('91', plain,
% 8.95/9.20      (![X8 : $i, X10 : $i]:
% 8.95/9.20         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 8.95/9.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.95/9.20  thf('92', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['90', '91'])).
% 8.95/9.20  thf('93', plain,
% 8.95/9.20      ((((sk_D) = (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 8.95/9.20        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['89', '92'])).
% 8.95/9.20  thf('94', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         (~ (v1_xboole_0 @ k1_xboole_0)
% 8.95/9.20          | (zip_tseitin_0 @ sk_B_2 @ X0)
% 8.95/9.20          | ((sk_D) = (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['86', '93'])).
% 8.95/9.20  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.95/9.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.95/9.20  thf('96', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         ((zip_tseitin_0 @ sk_B_2 @ X0)
% 8.95/9.20          | ((sk_D) = (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.95/9.20      inference('demod', [status(thm)], ['94', '95'])).
% 8.95/9.20  thf('97', plain,
% 8.95/9.20      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['0', '1'])).
% 8.95/9.20  thf('98', plain,
% 8.95/9.20      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 8.95/9.20      inference('simplify', [status(thm)], ['42'])).
% 8.95/9.20  thf('99', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup+', [status(thm)], ['97', '98'])).
% 8.95/9.20  thf('100', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         (((sk_D) = (k1_xboole_0))
% 8.95/9.20          | (zip_tseitin_0 @ sk_B_2 @ X0)
% 8.95/9.20          | ~ (v1_xboole_0 @ sk_B_2))),
% 8.95/9.20      inference('sup+', [status(thm)], ['96', '99'])).
% 8.95/9.20  thf('101', plain,
% 8.95/9.20      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['0', '1'])).
% 8.95/9.20  thf('102', plain,
% 8.95/9.20      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['0', '1'])).
% 8.95/9.20  thf('103', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 8.95/9.20      inference('sup+', [status(thm)], ['101', '102'])).
% 8.95/9.20  thf('104', plain, ((((sk_B_2) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.95/9.20  thf('105', plain,
% 8.95/9.20      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 8.95/9.20      inference('split', [status(esa)], ['104'])).
% 8.95/9.20  thf('106', plain,
% 8.95/9.20      ((![X0 : $i]:
% 8.95/9.20          (((X0) != (k1_xboole_0))
% 8.95/9.20           | ~ (v1_xboole_0 @ X0)
% 8.95/9.20           | ~ (v1_xboole_0 @ sk_B_2)))
% 8.95/9.20         <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['103', '105'])).
% 8.95/9.20  thf('107', plain,
% 8.95/9.20      (((~ (v1_xboole_0 @ sk_B_2) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 8.95/9.20         <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 8.95/9.20      inference('simplify', [status(thm)], ['106'])).
% 8.95/9.20  thf('108', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.95/9.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.95/9.20  thf('109', plain,
% 8.95/9.20      ((~ (v1_xboole_0 @ sk_B_2)) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 8.95/9.20      inference('simplify_reflect+', [status(thm)], ['107', '108'])).
% 8.95/9.20  thf('110', plain,
% 8.95/9.20      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 8.95/9.20      inference('demod', [status(thm)], ['38', '55'])).
% 8.95/9.20  thf('111', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['4', '5'])).
% 8.95/9.20  thf('112', plain,
% 8.95/9.20      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 8.95/9.20      inference('simplify', [status(thm)], ['15'])).
% 8.95/9.20  thf('113', plain,
% 8.95/9.20      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('split', [status(esa)], ['104'])).
% 8.95/9.20  thf('114', plain,
% 8.95/9.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.95/9.20  thf('115', plain,
% 8.95/9.20      (((m1_subset_1 @ sk_D @ 
% 8.95/9.20         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 8.95/9.20         <= ((((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('sup+', [status(thm)], ['113', '114'])).
% 8.95/9.20  thf('116', plain,
% 8.95/9.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 8.95/9.20         <= ((((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('sup+', [status(thm)], ['112', '115'])).
% 8.95/9.20  thf('117', plain,
% 8.95/9.20      (![X14 : $i, X15 : $i]:
% 8.95/9.20         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 8.95/9.20      inference('cnf', [status(esa)], [t3_subset])).
% 8.95/9.20  thf('118', plain,
% 8.95/9.20      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['116', '117'])).
% 8.95/9.20  thf('119', plain,
% 8.95/9.20      (![X8 : $i, X10 : $i]:
% 8.95/9.20         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 8.95/9.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.95/9.20  thf('120', plain,
% 8.95/9.20      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 8.95/9.20         <= ((((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['118', '119'])).
% 8.95/9.20  thf('121', plain,
% 8.95/9.20      (((~ (v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (sk_D))))
% 8.95/9.20         <= ((((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['111', '120'])).
% 8.95/9.20  thf('122', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.95/9.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.95/9.20  thf('123', plain,
% 8.95/9.20      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('demod', [status(thm)], ['121', '122'])).
% 8.95/9.20  thf('124', plain,
% 8.95/9.20      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('split', [status(esa)], ['104'])).
% 8.95/9.20  thf('125', plain,
% 8.95/9.20      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 8.95/9.20         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 8.95/9.20      inference('split', [status(esa)], ['59'])).
% 8.95/9.20  thf('126', plain,
% 8.95/9.20      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 8.95/9.20         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 8.95/9.20             (((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['124', '125'])).
% 8.95/9.20  thf('127', plain,
% 8.95/9.20      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 8.95/9.20         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 8.95/9.20             (((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['123', '126'])).
% 8.95/9.20  thf('128', plain,
% 8.95/9.20      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['110', '127'])).
% 8.95/9.20  thf('129', plain,
% 8.95/9.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 8.95/9.20         <= ((((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('sup+', [status(thm)], ['112', '115'])).
% 8.95/9.20  thf('130', plain,
% 8.95/9.20      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 8.95/9.20      inference('simplify', [status(thm)], ['15'])).
% 8.95/9.20  thf('131', plain,
% 8.95/9.20      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('split', [status(esa)], ['104'])).
% 8.95/9.20  thf('132', plain,
% 8.95/9.20      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 8.95/9.20         <= (~
% 8.95/9.20             ((m1_subset_1 @ sk_D @ 
% 8.95/9.20               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 8.95/9.20      inference('split', [status(esa)], ['59'])).
% 8.95/9.20  thf('133', plain,
% 8.95/9.20      ((~ (m1_subset_1 @ sk_D @ 
% 8.95/9.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 8.95/9.20         <= (~
% 8.95/9.20             ((m1_subset_1 @ sk_D @ 
% 8.95/9.20               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 8.95/9.20             (((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['131', '132'])).
% 8.95/9.20  thf('134', plain,
% 8.95/9.20      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 8.95/9.20         <= (~
% 8.95/9.20             ((m1_subset_1 @ sk_D @ 
% 8.95/9.20               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 8.95/9.20             (((sk_A) = (k1_xboole_0))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['130', '133'])).
% 8.95/9.20  thf('135', plain,
% 8.95/9.20      (~ (((sk_A) = (k1_xboole_0))) | 
% 8.95/9.20       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['129', '134'])).
% 8.95/9.20  thf('136', plain,
% 8.95/9.20      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 8.95/9.20       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 8.95/9.20      inference('split', [status(esa)], ['59'])).
% 8.95/9.20  thf('137', plain,
% 8.95/9.20      (~ (((sk_B_2) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 8.95/9.20      inference('split', [status(esa)], ['104'])).
% 8.95/9.20  thf('138', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 8.95/9.20      inference('sat_resolution*', [status(thm)],
% 8.95/9.20                ['63', '128', '135', '136', '137'])).
% 8.95/9.20  thf('139', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 8.95/9.20      inference('simpl_trail', [status(thm)], ['109', '138'])).
% 8.95/9.20  thf('140', plain,
% 8.95/9.20      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_2) | (zip_tseitin_0 @ sk_B_2 @ X0))),
% 8.95/9.20      inference('clc', [status(thm)], ['100', '139'])).
% 8.95/9.20  thf('141', plain,
% 8.95/9.20      (![X35 : $i, X36 : $i]:
% 8.95/9.20         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.95/9.20  thf('142', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.95/9.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.95/9.20  thf('143', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 8.95/9.20      inference('sup+', [status(thm)], ['141', '142'])).
% 8.95/9.20  thf('144', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_2 @ X0)),
% 8.95/9.20      inference('clc', [status(thm)], ['140', '143'])).
% 8.95/9.20  thf('145', plain, ((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)),
% 8.95/9.20      inference('demod', [status(thm)], ['83', '144'])).
% 8.95/9.20  thf('146', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 8.95/9.20      inference('demod', [status(thm)], ['80', '145'])).
% 8.95/9.20  thf('147', plain,
% 8.95/9.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.95/9.20  thf(cc2_relat_1, axiom,
% 8.95/9.20    (![A:$i]:
% 8.95/9.20     ( ( v1_relat_1 @ A ) =>
% 8.95/9.20       ( ![B:$i]:
% 8.95/9.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 8.95/9.20  thf('148', plain,
% 8.95/9.20      (![X20 : $i, X21 : $i]:
% 8.95/9.20         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 8.95/9.20          | (v1_relat_1 @ X20)
% 8.95/9.20          | ~ (v1_relat_1 @ X21))),
% 8.95/9.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.95/9.20  thf('149', plain,
% 8.95/9.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) | (v1_relat_1 @ sk_D))),
% 8.95/9.20      inference('sup-', [status(thm)], ['147', '148'])).
% 8.95/9.20  thf('150', plain,
% 8.95/9.20      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 8.95/9.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.95/9.20  thf('151', plain, ((v1_relat_1 @ sk_D)),
% 8.95/9.20      inference('demod', [status(thm)], ['149', '150'])).
% 8.95/9.20  thf('152', plain,
% 8.95/9.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 8.95/9.20      inference('demod', [status(thm)], ['73', '146', '151'])).
% 8.95/9.20  thf('153', plain,
% 8.95/9.20      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 8.95/9.20         <= (~
% 8.95/9.20             ((m1_subset_1 @ sk_D @ 
% 8.95/9.20               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 8.95/9.20      inference('split', [status(esa)], ['59'])).
% 8.95/9.20  thf('154', plain,
% 8.95/9.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 8.95/9.20      inference('sup-', [status(thm)], ['152', '153'])).
% 8.95/9.20  thf('155', plain,
% 8.95/9.20      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 8.95/9.20       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 8.95/9.20       ~ ((v1_funct_1 @ sk_D))),
% 8.95/9.20      inference('split', [status(esa)], ['59'])).
% 8.95/9.20  thf('156', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 8.95/9.20      inference('sat_resolution*', [status(thm)], ['63', '154', '155'])).
% 8.95/9.20  thf('157', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 8.95/9.20      inference('simpl_trail', [status(thm)], ['60', '156'])).
% 8.95/9.20  thf('158', plain, ((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 8.95/9.20      inference('sup-', [status(thm)], ['58', '157'])).
% 8.95/9.20  thf('159', plain,
% 8.95/9.20      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['0', '1'])).
% 8.95/9.20  thf('160', plain,
% 8.95/9.20      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 8.95/9.20      inference('simplify', [status(thm)], ['15'])).
% 8.95/9.20  thf('161', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup+', [status(thm)], ['159', '160'])).
% 8.95/9.20  thf('162', plain,
% 8.95/9.20      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 8.95/9.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 8.95/9.20  thf('163', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_2))),
% 8.95/9.20      inference('sup-', [status(thm)], ['87', '88'])).
% 8.95/9.20  thf('164', plain,
% 8.95/9.20      (![X3 : $i, X4 : $i, X5 : $i]:
% 8.95/9.20         (~ (r2_hidden @ X3 @ X4)
% 8.95/9.20          | (r2_hidden @ X3 @ X5)
% 8.95/9.20          | ~ (r1_tarski @ X4 @ X5))),
% 8.95/9.20      inference('cnf', [status(esa)], [d3_tarski])).
% 8.95/9.20  thf('165', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 8.95/9.20          | ~ (r2_hidden @ X0 @ sk_D))),
% 8.95/9.20      inference('sup-', [status(thm)], ['163', '164'])).
% 8.95/9.20  thf('166', plain,
% 8.95/9.20      (((v1_xboole_0 @ sk_D)
% 8.95/9.20        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['162', '165'])).
% 8.95/9.20  thf('167', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 8.95/9.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 8.95/9.20  thf('168', plain,
% 8.95/9.20      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['166', '167'])).
% 8.95/9.20  thf('169', plain,
% 8.95/9.20      ((~ (v1_xboole_0 @ k1_xboole_0)
% 8.95/9.20        | ~ (v1_xboole_0 @ sk_A)
% 8.95/9.20        | (v1_xboole_0 @ sk_D))),
% 8.95/9.20      inference('sup-', [status(thm)], ['161', '168'])).
% 8.95/9.20  thf('170', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.95/9.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.95/9.20  thf('171', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 8.95/9.20      inference('demod', [status(thm)], ['169', '170'])).
% 8.95/9.20  thf('172', plain, (~ (v1_xboole_0 @ sk_A)),
% 8.95/9.20      inference('clc', [status(thm)], ['158', '171'])).
% 8.95/9.20  thf('173', plain,
% 8.95/9.20      (![X35 : $i, X36 : $i]:
% 8.95/9.20         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.95/9.20  thf('174', plain,
% 8.95/9.20      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 8.95/9.20        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 8.95/9.20      inference('sup-', [status(thm)], ['81', '82'])).
% 8.95/9.20  thf('175', plain,
% 8.95/9.20      ((((sk_B_2) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 8.95/9.20      inference('sup-', [status(thm)], ['173', '174'])).
% 8.95/9.20  thf('176', plain,
% 8.95/9.20      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 8.95/9.20        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 8.95/9.20      inference('demod', [status(thm)], ['76', '79'])).
% 8.95/9.20  thf('177', plain,
% 8.95/9.20      ((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['175', '176'])).
% 8.95/9.20  thf('178', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 8.95/9.20      inference('sup+', [status(thm)], ['141', '142'])).
% 8.95/9.20  thf('179', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 8.95/9.20      inference('demod', [status(thm)], ['64', '67'])).
% 8.95/9.20  thf('180', plain,
% 8.95/9.20      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['0', '1'])).
% 8.95/9.20  thf('181', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 8.95/9.20      inference('sup-', [status(thm)], ['41', '49'])).
% 8.95/9.20  thf('182', plain,
% 8.95/9.20      (![X8 : $i, X10 : $i]:
% 8.95/9.20         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 8.95/9.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.95/9.20  thf('183', plain,
% 8.95/9.20      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['181', '182'])).
% 8.95/9.20  thf('184', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (~ (r1_tarski @ X1 @ X0)
% 8.95/9.20          | ~ (v1_xboole_0 @ X0)
% 8.95/9.20          | ((X1) = (k1_xboole_0)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['180', '183'])).
% 8.95/9.20  thf('185', plain,
% 8.95/9.20      ((((k2_relat_1 @ sk_D) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C_1))),
% 8.95/9.20      inference('sup-', [status(thm)], ['179', '184'])).
% 8.95/9.20  thf('186', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         ((zip_tseitin_0 @ sk_C_1 @ X0) | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['178', '185'])).
% 8.95/9.20  thf('187', plain,
% 8.95/9.20      (![X25 : $i]:
% 8.95/9.20         (((k2_relat_1 @ X25) != (k1_xboole_0))
% 8.95/9.20          | ((k1_relat_1 @ X25) = (k1_xboole_0))
% 8.95/9.20          | ~ (v1_relat_1 @ X25))),
% 8.95/9.20      inference('cnf', [status(esa)], [t65_relat_1])).
% 8.95/9.20  thf('188', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         (((k1_xboole_0) != (k1_xboole_0))
% 8.95/9.20          | (zip_tseitin_0 @ sk_C_1 @ X0)
% 8.95/9.20          | ~ (v1_relat_1 @ sk_D)
% 8.95/9.20          | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['186', '187'])).
% 8.95/9.20  thf('189', plain, ((v1_relat_1 @ sk_D)),
% 8.95/9.20      inference('demod', [status(thm)], ['149', '150'])).
% 8.95/9.20  thf('190', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         (((k1_xboole_0) != (k1_xboole_0))
% 8.95/9.20          | (zip_tseitin_0 @ sk_C_1 @ X0)
% 8.95/9.20          | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 8.95/9.20      inference('demod', [status(thm)], ['188', '189'])).
% 8.95/9.20  thf('191', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         (((k1_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C_1 @ X0))),
% 8.95/9.20      inference('simplify', [status(thm)], ['190'])).
% 8.95/9.20  thf('192', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         (((sk_A) = (k1_xboole_0))
% 8.95/9.20          | ((sk_B_2) = (k1_xboole_0))
% 8.95/9.20          | (zip_tseitin_0 @ sk_C_1 @ X0))),
% 8.95/9.20      inference('sup+', [status(thm)], ['177', '191'])).
% 8.95/9.20  thf('193', plain,
% 8.95/9.20      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 8.95/9.20      inference('split', [status(esa)], ['104'])).
% 8.95/9.20  thf('194', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 8.95/9.20      inference('sat_resolution*', [status(thm)],
% 8.95/9.20                ['63', '128', '135', '136', '137'])).
% 8.95/9.20  thf('195', plain, (((sk_B_2) != (k1_xboole_0))),
% 8.95/9.20      inference('simpl_trail', [status(thm)], ['193', '194'])).
% 8.95/9.20  thf('196', plain,
% 8.95/9.20      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C_1 @ X0))),
% 8.95/9.20      inference('simplify_reflect-', [status(thm)], ['192', '195'])).
% 8.95/9.20  thf('197', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 8.95/9.20      inference('sup-', [status(thm)], ['52', '53'])).
% 8.95/9.20  thf('198', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         (((sk_A) = (k1_xboole_0))
% 8.95/9.20          | (zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['196', '197'])).
% 8.95/9.20  thf('199', plain,
% 8.95/9.20      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['0', '1'])).
% 8.95/9.20  thf('200', plain,
% 8.95/9.20      (![X40 : $i, X41 : $i, X42 : $i]:
% 8.95/9.20         (((X40) != (k1_xboole_0))
% 8.95/9.20          | ((X41) = (k1_xboole_0))
% 8.95/9.20          | (v1_funct_2 @ X42 @ X41 @ X40)
% 8.95/9.20          | ((X42) != (k1_xboole_0))
% 8.95/9.20          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_4])).
% 8.95/9.20  thf('201', plain,
% 8.95/9.20      (![X41 : $i]:
% 8.95/9.20         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 8.95/9.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ k1_xboole_0)))
% 8.95/9.20          | (v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0)
% 8.95/9.20          | ((X41) = (k1_xboole_0)))),
% 8.95/9.20      inference('simplify', [status(thm)], ['200'])).
% 8.95/9.20  thf('202', plain,
% 8.95/9.20      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 8.95/9.20      inference('simplify', [status(thm)], ['42'])).
% 8.95/9.20  thf('203', plain,
% 8.95/9.20      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['50', '51'])).
% 8.95/9.20  thf('204', plain,
% 8.95/9.20      (![X41 : $i]:
% 8.95/9.20         ((v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0)
% 8.95/9.20          | ((X41) = (k1_xboole_0)))),
% 8.95/9.20      inference('demod', [status(thm)], ['201', '202', '203'])).
% 8.95/9.20  thf('205', plain,
% 8.95/9.20      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.95/9.20         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 8.95/9.20          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 8.95/9.20          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.95/9.20  thf('206', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         (((X0) = (k1_xboole_0))
% 8.95/9.20          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 8.95/9.20          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['204', '205'])).
% 8.95/9.20  thf('207', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 8.95/9.20      inference('demod', [status(thm)], ['33', '34'])).
% 8.95/9.20  thf('208', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         (((X0) = (k1_xboole_0))
% 8.95/9.20          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 8.95/9.20          | ((X0) = (k1_xboole_0)))),
% 8.95/9.20      inference('demod', [status(thm)], ['206', '207'])).
% 8.95/9.20  thf('209', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 8.95/9.20          | ((X0) = (k1_xboole_0)))),
% 8.95/9.20      inference('simplify', [status(thm)], ['208'])).
% 8.95/9.20  thf('210', plain,
% 8.95/9.20      (![X0 : $i, X1 : $i]:
% 8.95/9.20         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 8.95/9.20          | ~ (v1_xboole_0 @ X0)
% 8.95/9.20          | ((X1) = (k1_xboole_0)))),
% 8.95/9.20      inference('sup-', [status(thm)], ['199', '209'])).
% 8.95/9.20  thf('211', plain,
% 8.95/9.20      (![X0 : $i]:
% 8.95/9.20         (((sk_A) = (k1_xboole_0))
% 8.95/9.20          | ((X0) = (k1_xboole_0))
% 8.95/9.20          | ~ (v1_xboole_0 @ sk_C_1))),
% 8.95/9.20      inference('sup-', [status(thm)], ['198', '210'])).
% 8.95/9.20  thf('212', plain, ((((sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C_1))),
% 8.95/9.20      inference('condensation', [status(thm)], ['211'])).
% 8.95/9.20  thf('213', plain,
% 8.95/9.20      (![X35 : $i, X36 : $i]:
% 8.95/9.20         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.95/9.20  thf('214', plain,
% 8.95/9.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 8.95/9.20      inference('demod', [status(thm)], ['73', '146', '151'])).
% 8.95/9.20  thf('215', plain,
% 8.95/9.20      (![X40 : $i, X41 : $i, X42 : $i]:
% 8.95/9.20         (~ (zip_tseitin_0 @ X40 @ X41)
% 8.95/9.20          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 8.95/9.20          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_4])).
% 8.95/9.20  thf('216', plain,
% 8.95/9.20      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 8.95/9.20        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 8.95/9.20      inference('sup-', [status(thm)], ['214', '215'])).
% 8.95/9.20  thf('217', plain,
% 8.95/9.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 8.95/9.20      inference('demod', [status(thm)], ['73', '146', '151'])).
% 8.95/9.20  thf('218', plain,
% 8.95/9.20      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.95/9.20         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 8.95/9.20          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 8.95/9.20      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 8.95/9.20  thf('219', plain,
% 8.95/9.20      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 8.95/9.20      inference('sup-', [status(thm)], ['217', '218'])).
% 8.95/9.20  thf('220', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 8.95/9.20      inference('demod', [status(thm)], ['80', '145'])).
% 8.95/9.20  thf('221', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 8.95/9.20      inference('demod', [status(thm)], ['219', '220'])).
% 8.95/9.20  thf('222', plain,
% 8.95/9.20      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.95/9.20         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 8.95/9.20          | (v1_funct_2 @ X39 @ X37 @ X38)
% 8.95/9.20          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 8.95/9.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.95/9.20  thf('223', plain,
% 8.95/9.20      ((((sk_A) != (sk_A))
% 8.95/9.20        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 8.95/9.20        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 8.95/9.20      inference('sup-', [status(thm)], ['221', '222'])).
% 8.95/9.20  thf('224', plain,
% 8.95/9.20      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 8.95/9.20        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 8.95/9.20      inference('simplify', [status(thm)], ['223'])).
% 8.95/9.20  thf('225', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 8.95/9.20      inference('simpl_trail', [status(thm)], ['60', '156'])).
% 8.95/9.20  thf('226', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 8.95/9.20      inference('clc', [status(thm)], ['224', '225'])).
% 8.95/9.20  thf('227', plain, (~ (zip_tseitin_0 @ sk_C_1 @ sk_A)),
% 8.95/9.20      inference('clc', [status(thm)], ['216', '226'])).
% 8.95/9.20  thf('228', plain, (((sk_C_1) = (k1_xboole_0))),
% 8.95/9.20      inference('sup-', [status(thm)], ['213', '227'])).
% 8.95/9.20  thf('229', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.95/9.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.95/9.20  thf('230', plain, (((sk_A) = (k1_xboole_0))),
% 8.95/9.20      inference('demod', [status(thm)], ['212', '228', '229'])).
% 8.95/9.20  thf('231', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.95/9.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.95/9.20  thf('232', plain, ($false),
% 8.95/9.20      inference('demod', [status(thm)], ['172', '230', '231'])).
% 8.95/9.20  
% 8.95/9.20  % SZS output end Refutation
% 8.95/9.20  
% 8.95/9.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
