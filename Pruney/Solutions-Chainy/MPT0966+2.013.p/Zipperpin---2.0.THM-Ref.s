%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Bp1eONDjy

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:07 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  266 (4031 expanded)
%              Number of leaves         :   46 (1255 expanded)
%              Depth                    :   36
%              Number of atoms          : 1750 (34968 expanded)
%              Number of equality atoms :  161 (2756 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('14',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('15',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('23',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

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

thf('46',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40
       != ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('50',plain,(
    ! [X38: $i] :
      ( zip_tseitin_0 @ X38 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

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

thf('52',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','56'])).

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

thf('58',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('65',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_xboole_0
      = ( k6_relat_1 @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('72',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('73',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ( k1_xboole_0
      = ( k6_relat_1 @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('78',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('87',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('88',plain,(
    ! [X24: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('89',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('92',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','94'])).

thf('96',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('97',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['58'])).

thf('100',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['48','54'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('103',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('104',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['96'])).

thf('105',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('106',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('109',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('114',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['96'])).

thf('116',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['58'])).

thf('117',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','118'])).

thf('120',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('121',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('122',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['96'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['58'])).

thf('124',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['120','125'])).

thf('127',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['58'])).

thf('128',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['96'])).

thf('129',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['100','119','126','127','128'])).

thf('130',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['97','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['95','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('133',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['131','134'])).

thf('136',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(condensation,[status(thm)],['135'])).

thf('137',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['60','136'])).

thf('138',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('139',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('140',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('141',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['138','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('144',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('145',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('147',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('149',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('150',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('152',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['147','152'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('154',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X36 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['150','151'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['142','157'])).

thf('159',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['58'])).

thf('160',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['58'])).

thf('162',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['100','160','161'])).

thf('163',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['137','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['142','157'])).

thf('165',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('166',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('168',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('170',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['142','157'])).

thf('171',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('172',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['142','157'])).

thf('174',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('175',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( k1_xboole_0
      = ( k6_relat_1 @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('177',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('178',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( zip_tseitin_0 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X1 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( k1_xboole_0 = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['176','183'])).

thf('185',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['97','129'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 != k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ( X45 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('188',plain,(
    ! [X44: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X44 @ k1_xboole_0 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('190',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('191',plain,(
    ! [X44: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X44 @ k1_xboole_0 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['186','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['186','196'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(condensation,[status(thm)],['200'])).

thf('202',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['175','201'])).

thf('203',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40
       != ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['58'])).

thf('207',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['100','160','161'])).

thf('208',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['206','207'])).

thf('209',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['205','208'])).

thf('210',plain,(
    ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['172','209'])).

thf('211',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['169','210'])).

thf('212',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('213',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('214',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['169','210'])).

thf('215',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('216',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['168','211','212','213','214','215'])).

thf('217',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('218',plain,(
    $false ),
    inference(demod,[status(thm)],['163','216','217'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Bp1eONDjy
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:51:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.49/1.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.49/1.70  % Solved by: fo/fo7.sh
% 1.49/1.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.49/1.70  % done 1832 iterations in 1.232s
% 1.49/1.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.49/1.70  % SZS output start Refutation
% 1.49/1.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.49/1.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.49/1.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.49/1.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.49/1.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.49/1.70  thf(sk_D_type, type, sk_D: $i).
% 1.49/1.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.49/1.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.49/1.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.49/1.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.49/1.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.49/1.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.49/1.70  thf(sk_A_type, type, sk_A: $i).
% 1.49/1.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.49/1.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.49/1.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.49/1.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.49/1.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.49/1.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.49/1.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.49/1.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.49/1.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.49/1.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.49/1.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.49/1.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.49/1.70  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.49/1.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.49/1.70  thf(d3_tarski, axiom,
% 1.49/1.70    (![A:$i,B:$i]:
% 1.49/1.70     ( ( r1_tarski @ A @ B ) <=>
% 1.49/1.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.49/1.70  thf('1', plain,
% 1.49/1.70      (![X4 : $i, X6 : $i]:
% 1.49/1.70         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.49/1.70      inference('cnf', [status(esa)], [d3_tarski])).
% 1.49/1.70  thf(d1_xboole_0, axiom,
% 1.49/1.70    (![A:$i]:
% 1.49/1.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.49/1.70  thf('2', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.49/1.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.49/1.70  thf('3', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['1', '2'])).
% 1.49/1.70  thf('4', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['1', '2'])).
% 1.49/1.70  thf(d10_xboole_0, axiom,
% 1.49/1.70    (![A:$i,B:$i]:
% 1.49/1.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.49/1.70  thf('5', plain,
% 1.49/1.70      (![X7 : $i, X9 : $i]:
% 1.49/1.70         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.49/1.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.49/1.70  thf('6', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['4', '5'])).
% 1.49/1.70  thf('7', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['3', '6'])).
% 1.49/1.70  thf('8', plain,
% 1.49/1.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['0', '7'])).
% 1.49/1.70  thf('9', plain,
% 1.49/1.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['0', '7'])).
% 1.49/1.70  thf('10', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['1', '2'])).
% 1.49/1.70  thf('11', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['1', '2'])).
% 1.49/1.70  thf(t113_zfmisc_1, axiom,
% 1.49/1.70    (![A:$i,B:$i]:
% 1.49/1.70     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.49/1.70       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.49/1.70  thf('12', plain,
% 1.49/1.70      (![X11 : $i, X12 : $i]:
% 1.49/1.70         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 1.49/1.70          | ((X12) != (k1_xboole_0)))),
% 1.49/1.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.49/1.70  thf('13', plain,
% 1.49/1.70      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('simplify', [status(thm)], ['12'])).
% 1.49/1.70  thf(t29_relset_1, axiom,
% 1.49/1.70    (![A:$i]:
% 1.49/1.70     ( m1_subset_1 @
% 1.49/1.70       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.49/1.70  thf('14', plain,
% 1.49/1.70      (![X37 : $i]:
% 1.49/1.70         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 1.49/1.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 1.49/1.70      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.49/1.70  thf('15', plain,
% 1.49/1.70      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['13', '14'])).
% 1.49/1.70  thf(t3_subset, axiom,
% 1.49/1.70    (![A:$i,B:$i]:
% 1.49/1.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.49/1.70  thf('16', plain,
% 1.49/1.70      (![X13 : $i, X14 : $i]:
% 1.49/1.70         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.49/1.70      inference('cnf', [status(esa)], [t3_subset])).
% 1.49/1.70  thf('17', plain, ((r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 1.49/1.70      inference('sup-', [status(thm)], ['15', '16'])).
% 1.49/1.70  thf('18', plain,
% 1.49/1.70      (![X7 : $i, X9 : $i]:
% 1.49/1.70         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.49/1.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.49/1.70  thf('19', plain,
% 1.49/1.70      ((~ (r1_tarski @ k1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))
% 1.49/1.70        | ((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['17', '18'])).
% 1.49/1.70  thf('20', plain,
% 1.49/1.70      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.49/1.70        | ((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['11', '19'])).
% 1.49/1.70  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.49/1.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.49/1.70  thf('22', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.49/1.70      inference('demod', [status(thm)], ['20', '21'])).
% 1.49/1.70  thf(t71_relat_1, axiom,
% 1.49/1.70    (![A:$i]:
% 1.49/1.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.49/1.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.49/1.70  thf('23', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.49/1.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.49/1.70  thf('24', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['22', '23'])).
% 1.49/1.70  thf(d18_relat_1, axiom,
% 1.49/1.70    (![A:$i,B:$i]:
% 1.49/1.70     ( ( v1_relat_1 @ B ) =>
% 1.49/1.70       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.49/1.70  thf('25', plain,
% 1.49/1.70      (![X18 : $i, X19 : $i]:
% 1.49/1.70         (~ (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.49/1.70          | (v4_relat_1 @ X18 @ X19)
% 1.49/1.70          | ~ (v1_relat_1 @ X18))),
% 1.49/1.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.49/1.70  thf('26', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.49/1.70          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.49/1.70          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['24', '25'])).
% 1.49/1.70  thf('27', plain,
% 1.49/1.70      (![X11 : $i, X12 : $i]:
% 1.49/1.70         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 1.49/1.70          | ((X11) != (k1_xboole_0)))),
% 1.49/1.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.49/1.70  thf('28', plain,
% 1.49/1.70      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 1.49/1.70      inference('simplify', [status(thm)], ['27'])).
% 1.49/1.70  thf(fc6_relat_1, axiom,
% 1.49/1.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.49/1.70  thf('29', plain,
% 1.49/1.70      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 1.49/1.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.49/1.70  thf('30', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.49/1.70      inference('sup+', [status(thm)], ['28', '29'])).
% 1.49/1.70  thf('31', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         (~ (r1_tarski @ k1_xboole_0 @ X0) | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 1.49/1.70      inference('demod', [status(thm)], ['26', '30'])).
% 1.49/1.70  thf('32', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         (~ (v1_xboole_0 @ k1_xboole_0) | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['10', '31'])).
% 1.49/1.70  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.49/1.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.49/1.70  thf('34', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 1.49/1.70      inference('demod', [status(thm)], ['32', '33'])).
% 1.49/1.70  thf('35', plain,
% 1.49/1.70      (![X18 : $i, X19 : $i]:
% 1.49/1.70         (~ (v4_relat_1 @ X18 @ X19)
% 1.49/1.70          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.49/1.70          | ~ (v1_relat_1 @ X18))),
% 1.49/1.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.49/1.70  thf('36', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         (~ (v1_relat_1 @ k1_xboole_0)
% 1.49/1.70          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['34', '35'])).
% 1.49/1.70  thf('37', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.49/1.70      inference('sup+', [status(thm)], ['28', '29'])).
% 1.49/1.70  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['22', '23'])).
% 1.49/1.70  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.49/1.70      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.49/1.70  thf('40', plain,
% 1.49/1.70      (![X13 : $i, X15 : $i]:
% 1.49/1.70         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 1.49/1.70      inference('cnf', [status(esa)], [t3_subset])).
% 1.49/1.70  thf('41', plain,
% 1.49/1.70      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['39', '40'])).
% 1.49/1.70  thf(redefinition_k1_relset_1, axiom,
% 1.49/1.70    (![A:$i,B:$i,C:$i]:
% 1.49/1.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.49/1.70  thf('42', plain,
% 1.49/1.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.49/1.70         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.49/1.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.49/1.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.49/1.70  thf('43', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['41', '42'])).
% 1.49/1.70  thf('44', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['22', '23'])).
% 1.49/1.70  thf('45', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('demod', [status(thm)], ['43', '44'])).
% 1.49/1.70  thf(d1_funct_2, axiom,
% 1.49/1.70    (![A:$i,B:$i,C:$i]:
% 1.49/1.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.49/1.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.49/1.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.49/1.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.49/1.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.49/1.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.49/1.70  thf(zf_stmt_0, axiom,
% 1.49/1.70    (![C:$i,B:$i,A:$i]:
% 1.49/1.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.49/1.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.49/1.70  thf('46', plain,
% 1.49/1.70      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.49/1.70         (((X40) != (k1_relset_1 @ X40 @ X41 @ X42))
% 1.49/1.70          | (v1_funct_2 @ X42 @ X40 @ X41)
% 1.49/1.70          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.70  thf('47', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         (((X1) != (k1_xboole_0))
% 1.49/1.70          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.49/1.70          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['45', '46'])).
% 1.49/1.70  thf('48', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.49/1.70          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.49/1.70      inference('simplify', [status(thm)], ['47'])).
% 1.49/1.70  thf(zf_stmt_1, axiom,
% 1.49/1.70    (![B:$i,A:$i]:
% 1.49/1.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.49/1.70       ( zip_tseitin_0 @ B @ A ) ))).
% 1.49/1.70  thf('49', plain,
% 1.49/1.70      (![X38 : $i, X39 : $i]:
% 1.49/1.70         ((zip_tseitin_0 @ X38 @ X39) | ((X39) != (k1_xboole_0)))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.49/1.70  thf('50', plain, (![X38 : $i]: (zip_tseitin_0 @ X38 @ k1_xboole_0)),
% 1.49/1.70      inference('simplify', [status(thm)], ['49'])).
% 1.49/1.70  thf('51', plain,
% 1.49/1.70      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['39', '40'])).
% 1.49/1.70  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.49/1.70  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.49/1.70  thf(zf_stmt_4, axiom,
% 1.49/1.70    (![A:$i,B:$i,C:$i]:
% 1.49/1.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.49/1.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.49/1.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.49/1.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.49/1.70  thf('52', plain,
% 1.49/1.70      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.49/1.70         (~ (zip_tseitin_0 @ X43 @ X44)
% 1.49/1.70          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 1.49/1.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.49/1.70  thf('53', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.49/1.70      inference('sup-', [status(thm)], ['51', '52'])).
% 1.49/1.70  thf('54', plain,
% 1.49/1.70      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.49/1.70      inference('sup-', [status(thm)], ['50', '53'])).
% 1.49/1.70  thf('55', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.49/1.70      inference('demod', [status(thm)], ['48', '54'])).
% 1.49/1.70  thf('56', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['9', '55'])).
% 1.49/1.70  thf('57', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.70         ((v1_funct_2 @ X2 @ X0 @ X1)
% 1.49/1.70          | ~ (v1_xboole_0 @ X0)
% 1.49/1.70          | ~ (v1_xboole_0 @ X2))),
% 1.49/1.70      inference('sup+', [status(thm)], ['8', '56'])).
% 1.49/1.70  thf(t8_funct_2, conjecture,
% 1.49/1.70    (![A:$i,B:$i,C:$i,D:$i]:
% 1.49/1.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.49/1.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.49/1.70       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.49/1.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.49/1.70           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.49/1.70             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.49/1.70  thf(zf_stmt_5, negated_conjecture,
% 1.49/1.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.49/1.70        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.49/1.70            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.49/1.70          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.49/1.70            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.49/1.70              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.49/1.70                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.49/1.70    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 1.49/1.70  thf('58', plain,
% 1.49/1.70      ((~ (v1_funct_1 @ sk_D)
% 1.49/1.70        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 1.49/1.70        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.70  thf('59', plain,
% 1.49/1.70      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.49/1.70         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.49/1.70      inference('split', [status(esa)], ['58'])).
% 1.49/1.70  thf('60', plain,
% 1.49/1.70      (((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A)))
% 1.49/1.70         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['57', '59'])).
% 1.49/1.70  thf('61', plain,
% 1.49/1.70      (![X38 : $i, X39 : $i]:
% 1.49/1.70         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.49/1.70  thf('62', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.49/1.70      inference('demod', [status(thm)], ['20', '21'])).
% 1.49/1.70  thf('63', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         (((k1_xboole_0) = (k6_relat_1 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 1.49/1.70      inference('sup+', [status(thm)], ['61', '62'])).
% 1.49/1.70  thf('64', plain,
% 1.49/1.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.70  thf('65', plain,
% 1.49/1.70      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.49/1.70         (~ (zip_tseitin_0 @ X43 @ X44)
% 1.49/1.70          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 1.49/1.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.49/1.70  thf('66', plain,
% 1.49/1.70      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.49/1.70        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.49/1.70      inference('sup-', [status(thm)], ['64', '65'])).
% 1.49/1.70  thf('67', plain,
% 1.49/1.70      ((((k1_xboole_0) = (k6_relat_1 @ sk_B_1))
% 1.49/1.70        | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.49/1.70      inference('sup-', [status(thm)], ['63', '66'])).
% 1.49/1.70  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.70  thf('69', plain,
% 1.49/1.70      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.49/1.70         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 1.49/1.70          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 1.49/1.70          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.70  thf('70', plain,
% 1.49/1.70      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.49/1.70        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['68', '69'])).
% 1.49/1.70  thf('71', plain,
% 1.49/1.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.70  thf('72', plain,
% 1.49/1.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.49/1.70         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.49/1.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.49/1.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.49/1.70  thf('73', plain,
% 1.49/1.70      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.49/1.70      inference('sup-', [status(thm)], ['71', '72'])).
% 1.49/1.70  thf('74', plain,
% 1.49/1.70      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.49/1.70        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.49/1.70      inference('demod', [status(thm)], ['70', '73'])).
% 1.49/1.70  thf('75', plain,
% 1.49/1.70      ((((k1_xboole_0) = (k6_relat_1 @ sk_B_1))
% 1.49/1.70        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['67', '74'])).
% 1.49/1.70  thf('76', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.49/1.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.49/1.70  thf('77', plain,
% 1.49/1.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['0', '7'])).
% 1.49/1.70  thf('78', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['22', '23'])).
% 1.49/1.70  thf('79', plain,
% 1.49/1.70      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['77', '78'])).
% 1.49/1.70  thf('80', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.49/1.70      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.49/1.70  thf('81', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         ((r1_tarski @ (k1_relat_1 @ X0) @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['79', '80'])).
% 1.49/1.70  thf('82', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 1.49/1.70      inference('sup+', [status(thm)], ['76', '81'])).
% 1.49/1.70  thf('83', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.49/1.70          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.49/1.70          | (r1_tarski @ sk_B_1 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['75', '82'])).
% 1.49/1.70  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.49/1.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.49/1.70  thf('85', plain,
% 1.49/1.70      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | (r1_tarski @ sk_B_1 @ X0))),
% 1.49/1.70      inference('demod', [status(thm)], ['83', '84'])).
% 1.49/1.70  thf('86', plain,
% 1.49/1.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['0', '7'])).
% 1.49/1.70  thf('87', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.49/1.70      inference('demod', [status(thm)], ['20', '21'])).
% 1.49/1.70  thf('88', plain, (![X24 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 1.49/1.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.49/1.70  thf('89', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['87', '88'])).
% 1.49/1.70  thf('90', plain,
% 1.49/1.70      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['86', '89'])).
% 1.49/1.70  thf('91', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.49/1.70      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.49/1.70  thf('92', plain,
% 1.49/1.70      (![X7 : $i, X9 : $i]:
% 1.49/1.70         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.49/1.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.49/1.70  thf('93', plain,
% 1.49/1.70      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['91', '92'])).
% 1.49/1.70  thf('94', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         (~ (r1_tarski @ X1 @ (k2_relat_1 @ X0))
% 1.49/1.70          | ~ (v1_xboole_0 @ X0)
% 1.49/1.70          | ((X1) = (k1_xboole_0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['90', '93'])).
% 1.49/1.70  thf('95', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         (((sk_A) = (k1_relat_1 @ sk_D))
% 1.49/1.70          | ((sk_B_1) = (k1_xboole_0))
% 1.49/1.70          | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['85', '94'])).
% 1.49/1.70  thf('96', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.70  thf('97', plain,
% 1.49/1.70      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.49/1.70      inference('split', [status(esa)], ['96'])).
% 1.49/1.70  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.70  thf('99', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 1.49/1.70      inference('split', [status(esa)], ['58'])).
% 1.49/1.70  thf('100', plain, (((v1_funct_1 @ sk_D))),
% 1.49/1.70      inference('sup-', [status(thm)], ['98', '99'])).
% 1.49/1.70  thf('101', plain,
% 1.49/1.70      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.49/1.70      inference('demod', [status(thm)], ['48', '54'])).
% 1.49/1.70  thf('102', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['1', '2'])).
% 1.49/1.70  thf('103', plain,
% 1.49/1.70      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 1.49/1.70      inference('simplify', [status(thm)], ['27'])).
% 1.49/1.70  thf('104', plain,
% 1.49/1.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('split', [status(esa)], ['96'])).
% 1.49/1.70  thf('105', plain,
% 1.49/1.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.70  thf('106', plain,
% 1.49/1.70      (((m1_subset_1 @ sk_D @ 
% 1.49/1.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.49/1.70         <= ((((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('sup+', [status(thm)], ['104', '105'])).
% 1.49/1.70  thf('107', plain,
% 1.49/1.70      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.49/1.70         <= ((((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('sup+', [status(thm)], ['103', '106'])).
% 1.49/1.70  thf('108', plain,
% 1.49/1.70      (![X13 : $i, X14 : $i]:
% 1.49/1.70         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.49/1.70      inference('cnf', [status(esa)], [t3_subset])).
% 1.49/1.70  thf('109', plain,
% 1.49/1.70      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('sup-', [status(thm)], ['107', '108'])).
% 1.49/1.70  thf('110', plain,
% 1.49/1.70      (![X7 : $i, X9 : $i]:
% 1.49/1.70         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.49/1.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.49/1.70  thf('111', plain,
% 1.49/1.70      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 1.49/1.70         <= ((((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('sup-', [status(thm)], ['109', '110'])).
% 1.49/1.70  thf('112', plain,
% 1.49/1.70      (((~ (v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (sk_D))))
% 1.49/1.70         <= ((((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('sup-', [status(thm)], ['102', '111'])).
% 1.49/1.70  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.49/1.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.49/1.70  thf('114', plain,
% 1.49/1.70      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('demod', [status(thm)], ['112', '113'])).
% 1.49/1.70  thf('115', plain,
% 1.49/1.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('split', [status(esa)], ['96'])).
% 1.49/1.70  thf('116', plain,
% 1.49/1.70      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.49/1.70         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.49/1.70      inference('split', [status(esa)], ['58'])).
% 1.49/1.70  thf('117', plain,
% 1.49/1.70      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 1.49/1.70         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 1.49/1.70             (((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('sup-', [status(thm)], ['115', '116'])).
% 1.49/1.70  thf('118', plain,
% 1.49/1.70      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 1.49/1.70         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 1.49/1.70             (((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('sup-', [status(thm)], ['114', '117'])).
% 1.49/1.70  thf('119', plain,
% 1.49/1.70      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['101', '118'])).
% 1.49/1.70  thf('120', plain,
% 1.49/1.70      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.49/1.70         <= ((((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('sup+', [status(thm)], ['103', '106'])).
% 1.49/1.70  thf('121', plain,
% 1.49/1.70      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 1.49/1.70      inference('simplify', [status(thm)], ['27'])).
% 1.49/1.70  thf('122', plain,
% 1.49/1.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('split', [status(esa)], ['96'])).
% 1.49/1.70  thf('123', plain,
% 1.49/1.70      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 1.49/1.70         <= (~
% 1.49/1.70             ((m1_subset_1 @ sk_D @ 
% 1.49/1.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 1.49/1.70      inference('split', [status(esa)], ['58'])).
% 1.49/1.70  thf('124', plain,
% 1.49/1.70      ((~ (m1_subset_1 @ sk_D @ 
% 1.49/1.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 1.49/1.70         <= (~
% 1.49/1.70             ((m1_subset_1 @ sk_D @ 
% 1.49/1.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 1.49/1.70             (((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('sup-', [status(thm)], ['122', '123'])).
% 1.49/1.70  thf('125', plain,
% 1.49/1.70      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.49/1.70         <= (~
% 1.49/1.70             ((m1_subset_1 @ sk_D @ 
% 1.49/1.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 1.49/1.70             (((sk_A) = (k1_xboole_0))))),
% 1.49/1.70      inference('sup-', [status(thm)], ['121', '124'])).
% 1.49/1.70  thf('126', plain,
% 1.49/1.70      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.49/1.70       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.49/1.70      inference('sup-', [status(thm)], ['120', '125'])).
% 1.49/1.70  thf('127', plain,
% 1.49/1.70      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 1.49/1.70       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 1.49/1.70      inference('split', [status(esa)], ['58'])).
% 1.49/1.70  thf('128', plain,
% 1.49/1.70      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.49/1.70      inference('split', [status(esa)], ['96'])).
% 1.49/1.70  thf('129', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 1.49/1.70      inference('sat_resolution*', [status(thm)],
% 1.49/1.70                ['100', '119', '126', '127', '128'])).
% 1.49/1.70  thf('130', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.49/1.70      inference('simpl_trail', [status(thm)], ['97', '129'])).
% 1.49/1.70  thf('131', plain,
% 1.49/1.70      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('simplify_reflect-', [status(thm)], ['95', '130'])).
% 1.49/1.70  thf('132', plain,
% 1.49/1.70      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['77', '78'])).
% 1.49/1.70  thf('133', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.49/1.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.49/1.70  thf('134', plain,
% 1.49/1.70      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['132', '133'])).
% 1.49/1.70  thf('135', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         ((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 1.49/1.70      inference('sup+', [status(thm)], ['131', '134'])).
% 1.49/1.70  thf('136', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 1.49/1.70      inference('condensation', [status(thm)], ['135'])).
% 1.49/1.70  thf('137', plain,
% 1.49/1.70      ((~ (v1_xboole_0 @ sk_D)) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.49/1.70      inference('clc', [status(thm)], ['60', '136'])).
% 1.49/1.70  thf('138', plain,
% 1.49/1.70      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C_1)),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.70  thf('139', plain,
% 1.49/1.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.70  thf(redefinition_k2_relset_1, axiom,
% 1.49/1.70    (![A:$i,B:$i,C:$i]:
% 1.49/1.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.49/1.70  thf('140', plain,
% 1.49/1.70      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.49/1.70         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 1.49/1.70          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.49/1.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.49/1.70  thf('141', plain,
% 1.49/1.70      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.49/1.70      inference('sup-', [status(thm)], ['139', '140'])).
% 1.49/1.70  thf('142', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 1.49/1.70      inference('demod', [status(thm)], ['138', '141'])).
% 1.49/1.70  thf('143', plain,
% 1.49/1.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.70  thf(cc2_relset_1, axiom,
% 1.49/1.70    (![A:$i,B:$i,C:$i]:
% 1.49/1.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.49/1.70  thf('144', plain,
% 1.49/1.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.49/1.70         ((v4_relat_1 @ X25 @ X26)
% 1.49/1.70          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.49/1.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.49/1.70  thf('145', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.49/1.70      inference('sup-', [status(thm)], ['143', '144'])).
% 1.49/1.70  thf('146', plain,
% 1.49/1.70      (![X18 : $i, X19 : $i]:
% 1.49/1.70         (~ (v4_relat_1 @ X18 @ X19)
% 1.49/1.70          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.49/1.70          | ~ (v1_relat_1 @ X18))),
% 1.49/1.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.49/1.70  thf('147', plain,
% 1.49/1.70      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 1.49/1.70      inference('sup-', [status(thm)], ['145', '146'])).
% 1.49/1.70  thf('148', plain,
% 1.49/1.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.70  thf(cc2_relat_1, axiom,
% 1.49/1.70    (![A:$i]:
% 1.49/1.70     ( ( v1_relat_1 @ A ) =>
% 1.49/1.70       ( ![B:$i]:
% 1.49/1.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.49/1.70  thf('149', plain,
% 1.49/1.70      (![X16 : $i, X17 : $i]:
% 1.49/1.70         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.49/1.70          | (v1_relat_1 @ X16)
% 1.49/1.70          | ~ (v1_relat_1 @ X17))),
% 1.49/1.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.49/1.70  thf('150', plain,
% 1.49/1.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 1.49/1.70      inference('sup-', [status(thm)], ['148', '149'])).
% 1.49/1.70  thf('151', plain,
% 1.49/1.70      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 1.49/1.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.49/1.70  thf('152', plain, ((v1_relat_1 @ sk_D)),
% 1.49/1.70      inference('demod', [status(thm)], ['150', '151'])).
% 1.49/1.70  thf('153', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 1.49/1.70      inference('demod', [status(thm)], ['147', '152'])).
% 1.49/1.70  thf(t11_relset_1, axiom,
% 1.49/1.70    (![A:$i,B:$i,C:$i]:
% 1.49/1.70     ( ( v1_relat_1 @ C ) =>
% 1.49/1.70       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.49/1.70           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.49/1.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.49/1.70  thf('154', plain,
% 1.49/1.70      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.49/1.70         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 1.49/1.70          | ~ (r1_tarski @ (k2_relat_1 @ X34) @ X36)
% 1.49/1.70          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.49/1.70          | ~ (v1_relat_1 @ X34))),
% 1.49/1.70      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.49/1.70  thf('155', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         (~ (v1_relat_1 @ sk_D)
% 1.49/1.70          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.49/1.70          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['153', '154'])).
% 1.49/1.70  thf('156', plain, ((v1_relat_1 @ sk_D)),
% 1.49/1.70      inference('demod', [status(thm)], ['150', '151'])).
% 1.49/1.70  thf('157', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.49/1.70          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.49/1.70      inference('demod', [status(thm)], ['155', '156'])).
% 1.49/1.70  thf('158', plain,
% 1.49/1.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['142', '157'])).
% 1.49/1.70  thf('159', plain,
% 1.49/1.70      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 1.49/1.70         <= (~
% 1.49/1.70             ((m1_subset_1 @ sk_D @ 
% 1.49/1.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 1.49/1.70      inference('split', [status(esa)], ['58'])).
% 1.49/1.70  thf('160', plain,
% 1.49/1.70      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.49/1.70      inference('sup-', [status(thm)], ['158', '159'])).
% 1.49/1.70  thf('161', plain,
% 1.49/1.70      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 1.49/1.70       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 1.49/1.70       ~ ((v1_funct_1 @ sk_D))),
% 1.49/1.70      inference('split', [status(esa)], ['58'])).
% 1.49/1.70  thf('162', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.49/1.70      inference('sat_resolution*', [status(thm)], ['100', '160', '161'])).
% 1.49/1.70  thf('163', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.49/1.70      inference('simpl_trail', [status(thm)], ['137', '162'])).
% 1.49/1.70  thf('164', plain,
% 1.49/1.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['142', '157'])).
% 1.49/1.70  thf('165', plain,
% 1.49/1.70      (![X13 : $i, X14 : $i]:
% 1.49/1.70         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.49/1.70      inference('cnf', [status(esa)], [t3_subset])).
% 1.49/1.70  thf('166', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 1.49/1.70      inference('sup-', [status(thm)], ['164', '165'])).
% 1.49/1.70  thf('167', plain,
% 1.49/1.70      (![X7 : $i, X9 : $i]:
% 1.49/1.70         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.49/1.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.49/1.70  thf('168', plain,
% 1.49/1.70      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ sk_D)
% 1.49/1.70        | ((k2_zfmisc_1 @ sk_A @ sk_C_1) = (sk_D)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['166', '167'])).
% 1.49/1.70  thf('169', plain,
% 1.49/1.70      (![X38 : $i, X39 : $i]:
% 1.49/1.70         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.49/1.70  thf('170', plain,
% 1.49/1.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['142', '157'])).
% 1.49/1.70  thf('171', plain,
% 1.49/1.70      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.49/1.70         (~ (zip_tseitin_0 @ X43 @ X44)
% 1.49/1.70          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 1.49/1.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.49/1.70  thf('172', plain,
% 1.49/1.70      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 1.49/1.70        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 1.49/1.70      inference('sup-', [status(thm)], ['170', '171'])).
% 1.49/1.70  thf('173', plain,
% 1.49/1.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['142', '157'])).
% 1.49/1.70  thf('174', plain,
% 1.49/1.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.49/1.70         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.49/1.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.49/1.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.49/1.70  thf('175', plain,
% 1.49/1.70      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.49/1.70      inference('sup-', [status(thm)], ['173', '174'])).
% 1.49/1.70  thf('176', plain,
% 1.49/1.70      ((((k1_xboole_0) = (k6_relat_1 @ sk_B_1))
% 1.49/1.70        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['67', '74'])).
% 1.49/1.70  thf('177', plain,
% 1.49/1.70      (![X38 : $i, X39 : $i]:
% 1.49/1.70         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.49/1.70  thf('178', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('sup+', [status(thm)], ['22', '23'])).
% 1.49/1.70  thf('179', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         (((k1_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 1.49/1.70      inference('sup+', [status(thm)], ['177', '178'])).
% 1.49/1.70  thf('180', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.49/1.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.49/1.70  thf('181', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         (((k1_xboole_0) = (X0)) | (zip_tseitin_0 @ (k6_relat_1 @ X0) @ X1))),
% 1.49/1.70      inference('sup+', [status(thm)], ['179', '180'])).
% 1.49/1.70  thf('182', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.49/1.70      inference('sup-', [status(thm)], ['51', '52'])).
% 1.49/1.70  thf('183', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         (((k1_xboole_0) = (X1))
% 1.49/1.70          | (zip_tseitin_1 @ k1_xboole_0 @ (k6_relat_1 @ X1) @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['181', '182'])).
% 1.49/1.70  thf('184', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         ((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.49/1.70          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.49/1.70          | ((k1_xboole_0) = (sk_B_1)))),
% 1.49/1.70      inference('sup+', [status(thm)], ['176', '183'])).
% 1.49/1.70  thf('185', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.49/1.70      inference('simpl_trail', [status(thm)], ['97', '129'])).
% 1.49/1.70  thf('186', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         ((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.49/1.70          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.49/1.70      inference('simplify_reflect-', [status(thm)], ['184', '185'])).
% 1.49/1.70  thf('187', plain,
% 1.49/1.70      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.49/1.70         (((X43) != (k1_xboole_0))
% 1.49/1.70          | ((X44) = (k1_xboole_0))
% 1.49/1.70          | (v1_funct_2 @ X45 @ X44 @ X43)
% 1.49/1.70          | ((X45) != (k1_xboole_0))
% 1.49/1.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.49/1.70  thf('188', plain,
% 1.49/1.70      (![X44 : $i]:
% 1.49/1.70         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 1.49/1.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ k1_xboole_0)))
% 1.49/1.70          | (v1_funct_2 @ k1_xboole_0 @ X44 @ k1_xboole_0)
% 1.49/1.70          | ((X44) = (k1_xboole_0)))),
% 1.49/1.70      inference('simplify', [status(thm)], ['187'])).
% 1.49/1.70  thf('189', plain,
% 1.49/1.70      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('simplify', [status(thm)], ['12'])).
% 1.49/1.70  thf('190', plain,
% 1.49/1.70      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['39', '40'])).
% 1.49/1.70  thf('191', plain,
% 1.49/1.70      (![X44 : $i]:
% 1.49/1.70         ((v1_funct_2 @ k1_xboole_0 @ X44 @ k1_xboole_0)
% 1.49/1.70          | ((X44) = (k1_xboole_0)))),
% 1.49/1.70      inference('demod', [status(thm)], ['188', '189', '190'])).
% 1.49/1.70  thf('192', plain,
% 1.49/1.70      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.49/1.70         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 1.49/1.70          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 1.49/1.70          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.70  thf('193', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         (((X0) = (k1_xboole_0))
% 1.49/1.70          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.49/1.70          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['191', '192'])).
% 1.49/1.70  thf('194', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('demod', [status(thm)], ['43', '44'])).
% 1.49/1.70  thf('195', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         (((X0) = (k1_xboole_0))
% 1.49/1.70          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.49/1.70          | ((X0) = (k1_xboole_0)))),
% 1.49/1.70      inference('demod', [status(thm)], ['193', '194'])).
% 1.49/1.70  thf('196', plain,
% 1.49/1.70      (![X0 : $i]:
% 1.49/1.70         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.49/1.70          | ((X0) = (k1_xboole_0)))),
% 1.49/1.70      inference('simplify', [status(thm)], ['195'])).
% 1.49/1.70  thf('197', plain,
% 1.49/1.70      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X0) = (k1_xboole_0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['186', '196'])).
% 1.49/1.70  thf('198', plain,
% 1.49/1.70      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X0) = (k1_xboole_0)))),
% 1.49/1.70      inference('sup-', [status(thm)], ['186', '196'])).
% 1.49/1.70  thf('199', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]:
% 1.49/1.70         (((X1) = (X0))
% 1.49/1.70          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.49/1.70          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.49/1.70      inference('sup+', [status(thm)], ['197', '198'])).
% 1.49/1.70  thf('200', plain,
% 1.49/1.70      (![X0 : $i, X1 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X1) = (X0)))),
% 1.49/1.70      inference('simplify', [status(thm)], ['199'])).
% 1.49/1.70  thf('201', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.49/1.70      inference('condensation', [status(thm)], ['200'])).
% 1.49/1.70  thf('202', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 1.49/1.70      inference('demod', [status(thm)], ['175', '201'])).
% 1.49/1.70  thf('203', plain,
% 1.49/1.70      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.49/1.70         (((X40) != (k1_relset_1 @ X40 @ X41 @ X42))
% 1.49/1.70          | (v1_funct_2 @ X42 @ X40 @ X41)
% 1.49/1.70          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 1.49/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.70  thf('204', plain,
% 1.49/1.70      ((((sk_A) != (sk_A))
% 1.49/1.70        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 1.49/1.70        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.49/1.70      inference('sup-', [status(thm)], ['202', '203'])).
% 1.49/1.70  thf('205', plain,
% 1.49/1.70      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 1.49/1.70        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 1.49/1.70      inference('simplify', [status(thm)], ['204'])).
% 1.49/1.70  thf('206', plain,
% 1.49/1.70      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.49/1.70         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.49/1.70      inference('split', [status(esa)], ['58'])).
% 1.49/1.70  thf('207', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.49/1.70      inference('sat_resolution*', [status(thm)], ['100', '160', '161'])).
% 1.49/1.70  thf('208', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 1.49/1.70      inference('simpl_trail', [status(thm)], ['206', '207'])).
% 1.49/1.70  thf('209', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 1.49/1.70      inference('clc', [status(thm)], ['205', '208'])).
% 1.49/1.70  thf('210', plain, (~ (zip_tseitin_0 @ sk_C_1 @ sk_A)),
% 1.49/1.70      inference('clc', [status(thm)], ['172', '209'])).
% 1.49/1.70  thf('211', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['169', '210'])).
% 1.49/1.70  thf('212', plain,
% 1.49/1.70      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('simplify', [status(thm)], ['12'])).
% 1.49/1.70  thf('213', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.49/1.70      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.49/1.70  thf('214', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.49/1.70      inference('sup-', [status(thm)], ['169', '210'])).
% 1.49/1.70  thf('215', plain,
% 1.49/1.70      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.70      inference('simplify', [status(thm)], ['12'])).
% 1.49/1.70  thf('216', plain, (((k1_xboole_0) = (sk_D))),
% 1.49/1.70      inference('demod', [status(thm)],
% 1.49/1.70                ['168', '211', '212', '213', '214', '215'])).
% 1.49/1.70  thf('217', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.49/1.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.49/1.70  thf('218', plain, ($false),
% 1.49/1.70      inference('demod', [status(thm)], ['163', '216', '217'])).
% 1.49/1.70  
% 1.49/1.70  % SZS output end Refutation
% 1.49/1.70  
% 1.49/1.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
