%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h4IZecA17W

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:28 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 138 expanded)
%              Number of leaves         :   37 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  599 (1543 expanded)
%              Number of equality atoms :   36 (  76 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_2 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_2 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
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

thf('14',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('17',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('20',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ sk_C_2 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X20 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('25',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('27',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

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
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ),
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
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['22','31'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('34',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['21','34'])).

thf('36',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['18','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['15','36','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['12','40'])).

thf('42',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_2 @ X37 )
       != sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) )
 != sk_C_2 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ sk_C_2 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('45',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('46',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_C_2
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('50',plain,
    ( sk_C_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['43','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h4IZecA17W
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:35:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 213 iterations in 0.157s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.37/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.61  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.37/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.61  thf(t17_funct_2, conjecture,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.37/0.61            ( ![E:$i]:
% 0.37/0.61              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.61            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.37/0.61               ( ![E:$i]:
% 0.37/0.61                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.37/0.61                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      ((r2_hidden @ sk_C_2 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_2))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.61         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.37/0.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf('4', plain, ((r2_hidden @ sk_C_2 @ (k2_relat_1 @ sk_D_2))),
% 0.37/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.61  thf(d5_funct_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.37/0.61           ( ![C:$i]:
% 0.37/0.61             ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.61               ( ?[D:$i]:
% 0.37/0.61                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.37/0.61                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         (((X11) != (k2_relat_1 @ X9))
% 0.37/0.61          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9))
% 0.37/0.61          | ~ (r2_hidden @ X12 @ X11)
% 0.37/0.61          | ~ (v1_funct_1 @ X9)
% 0.37/0.61          | ~ (v1_relat_1 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X9 : $i, X12 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X9)
% 0.37/0.61          | ~ (v1_funct_1 @ X9)
% 0.37/0.61          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.37/0.61          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (((r2_hidden @ (sk_D_1 @ sk_C_2 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.37/0.61        | ~ (v1_funct_1 @ sk_D_2)
% 0.37/0.61        | ~ (v1_relat_1 @ sk_D_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['4', '6'])).
% 0.37/0.61  thf('8', plain, ((v1_funct_1 @ sk_D_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(cc1_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( v1_relat_1 @ C ) ))).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.61         ((v1_relat_1 @ X17)
% 0.37/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.61  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 0.37/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      ((r2_hidden @ (sk_D_1 @ sk_C_2 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.37/0.61      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.37/0.61  thf('13', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(d1_funct_2, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_1, axiom,
% 0.37/0.61    (![C:$i,B:$i,A:$i]:
% 0.37/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.37/0.61         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.37/0.61          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.37/0.61          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.37/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.61  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.61  thf(zf_stmt_4, axiom,
% 0.37/0.61    (![B:$i,A:$i]:
% 0.37/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.61  thf(zf_stmt_5, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.37/0.61         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.37/0.61          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.37/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.37/0.61        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      (![X29 : $i, X30 : $i]:
% 0.37/0.61         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.37/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.61  thf('20', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.37/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.37/0.61      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.61  thf('22', plain, ((r2_hidden @ sk_C_2 @ (k2_relat_1 @ sk_D_2))),
% 0.37/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(dt_k2_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.61         ((m1_subset_1 @ (k2_relset_1 @ X20 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 0.37/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_2) @ 
% 0.37/0.61        (k1_zfmisc_1 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.61  thf(t3_subset, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X5 : $i, X6 : $i]:
% 0.37/0.61         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('29', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B)),
% 0.37/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.61  thf(d3_tarski, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.61          | (r2_hidden @ X0 @ X2)
% 0.37/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.61  thf('32', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.37/0.61      inference('sup-', [status(thm)], ['22', '31'])).
% 0.37/0.61  thf(t7_ordinal1, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      (![X15 : $i, X16 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.37/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.61  thf('34', plain, (~ (r1_tarski @ sk_B @ sk_C_2)),
% 0.37/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf('35', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.37/0.61      inference('sup-', [status(thm)], ['21', '34'])).
% 0.37/0.61  thf('36', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)),
% 0.37/0.61      inference('demod', [status(thm)], ['18', '35'])).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.61         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.37/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.61  thf('40', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.37/0.61      inference('demod', [status(thm)], ['15', '36', '39'])).
% 0.37/0.61  thf('41', plain, ((r2_hidden @ (sk_D_1 @ sk_C_2 @ sk_D_2) @ sk_A)),
% 0.37/0.61      inference('demod', [status(thm)], ['12', '40'])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      (![X37 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X37 @ sk_A)
% 0.37/0.61          | ((k1_funct_1 @ sk_D_2 @ X37) != (sk_C_2)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (((k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_2 @ sk_D_2)) != (sk_C_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.61  thf('44', plain, ((r2_hidden @ sk_C_2 @ (k2_relat_1 @ sk_D_2))),
% 0.37/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         (((X11) != (k2_relat_1 @ X9))
% 0.37/0.61          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9)))
% 0.37/0.61          | ~ (r2_hidden @ X12 @ X11)
% 0.37/0.61          | ~ (v1_funct_1 @ X9)
% 0.37/0.61          | ~ (v1_relat_1 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X9 : $i, X12 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X9)
% 0.37/0.61          | ~ (v1_funct_1 @ X9)
% 0.37/0.61          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.37/0.61          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.37/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      ((((sk_C_2) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_2 @ sk_D_2)))
% 0.37/0.61        | ~ (v1_funct_1 @ sk_D_2)
% 0.37/0.61        | ~ (v1_relat_1 @ sk_D_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['44', '46'])).
% 0.37/0.61  thf('48', plain, ((v1_funct_1 @ sk_D_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('49', plain, ((v1_relat_1 @ sk_D_2)),
% 0.37/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.61  thf('50', plain,
% 0.37/0.61      (((sk_C_2) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_2 @ sk_D_2)))),
% 0.37/0.61      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.37/0.61  thf('51', plain, (((sk_C_2) != (sk_C_2))),
% 0.37/0.61      inference('demod', [status(thm)], ['43', '50'])).
% 0.37/0.61  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
