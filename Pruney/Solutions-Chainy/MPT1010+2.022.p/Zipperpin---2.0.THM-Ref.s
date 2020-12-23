%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8yshZZk5UJ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:16 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 123 expanded)
%              Number of leaves         :   42 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  616 (1065 expanded)
%              Number of equality atoms :   46 (  69 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( v5_relat_1 @ X55 @ X57 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v5_relat_1 @ X41 @ X42 )
      | ( r1_tarski @ ( k2_relat_1 @ X41 ) @ X42 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( v1_relat_1 @ X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B ) ),
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

thf('13',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( v1_funct_2 @ X65 @ X63 @ X64 )
      | ( X63
        = ( k1_relset_1 @ X63 @ X64 @ X65 ) )
      | ~ ( zip_tseitin_1 @ X65 @ X64 @ X63 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X61: $i,X62: $i] :
      ( ( zip_tseitin_0 @ X61 @ X62 )
      | ( X61 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('17',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( zip_tseitin_0 @ X66 @ X67 )
      | ( zip_tseitin_1 @ X68 @ X66 @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X67 @ X66 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ X37 @ X38 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X37 @ X39 ) @ X38 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('28',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 != X35 )
      | ~ ( r2_hidden @ X33 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('29',plain,(
    ! [X34: $i,X35: $i] :
      ~ ( r2_hidden @ X35 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['24','30'])).

thf('32',plain,(
    zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['19','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( ( k1_relset_1 @ X59 @ X60 @ X58 )
        = ( k1_relat_1 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('35',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['14','32','35'])).

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

thf('37',plain,(
    ! [X44: $i,X46: $i,X48: $i,X49: $i] :
      ( ( X46
       != ( k2_relat_1 @ X44 ) )
      | ( r2_hidden @ X48 @ X46 )
      | ~ ( r2_hidden @ X49 @ ( k1_relat_1 @ X44 ) )
      | ( X48
       != ( k1_funct_1 @ X44 @ X49 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('38',plain,(
    ! [X44: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( r2_hidden @ X49 @ ( k1_relat_1 @ X44 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X44 @ X49 ) @ ( k2_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['11','42'])).

thf('44',plain,(
    ! [X33: $i,X34: $i,X36: $i] :
      ( ( r2_hidden @ X33 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X36 ) ) )
      | ( X33 = X36 )
      | ~ ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
        = X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['10','45'])).

thf('47',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('50',plain,(
    $false ),
    inference('sup-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8yshZZk5UJ
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 273 iterations in 0.149s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.61  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.61  thf(t65_funct_2, conjecture,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.61         ( m1_subset_1 @
% 0.42/0.61           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.61       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.61            ( m1_subset_1 @
% 0.42/0.61              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.61          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.42/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(cc2_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.42/0.61         ((v5_relat_1 @ X55 @ X57)
% 0.42/0.61          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.61  thf('2', plain, ((v5_relat_1 @ sk_D_2 @ (k1_tarski @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.61  thf(d19_relat_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ B ) =>
% 0.42/0.61       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X41 : $i, X42 : $i]:
% 0.42/0.61         (~ (v5_relat_1 @ X41 @ X42)
% 0.42/0.61          | (r1_tarski @ (k2_relat_1 @ X41) @ X42)
% 0.42/0.61          | ~ (v1_relat_1 @ X41))),
% 0.42/0.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ sk_D_2)
% 0.42/0.61        | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.42/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(cc1_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( v1_relat_1 @ C ) ))).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.42/0.61         ((v1_relat_1 @ X52)
% 0.42/0.61          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.61  thf('7', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B))),
% 0.42/0.61      inference('demod', [status(thm)], ['4', '7'])).
% 0.42/0.61  thf(l32_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X0 : $i, X2 : $i]:
% 0.42/0.61         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (((k4_xboole_0 @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B))
% 0.42/0.61         = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.61  thf('11', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('12', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(d1_funct_2, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_1, axiom,
% 0.42/0.61    (![C:$i,B:$i,A:$i]:
% 0.42/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.42/0.61         (~ (v1_funct_2 @ X65 @ X63 @ X64)
% 0.42/0.61          | ((X63) = (k1_relset_1 @ X63 @ X64 @ X65))
% 0.42/0.61          | ~ (zip_tseitin_1 @ X65 @ X64 @ X63))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      ((~ (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.42/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.61  thf(zf_stmt_2, axiom,
% 0.42/0.61    (![B:$i,A:$i]:
% 0.42/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (![X61 : $i, X62 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X61 @ X62) | ((X61) = (k1_xboole_0)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.42/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.61  thf(zf_stmt_5, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.42/0.61         (~ (zip_tseitin_0 @ X66 @ X67)
% 0.42/0.61          | (zip_tseitin_1 @ X68 @ X66 @ X67)
% 0.42/0.61          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X67 @ X66))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (((zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.42/0.61        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.42/0.61        | (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['15', '18'])).
% 0.42/0.61  thf(t3_boole, axiom,
% 0.42/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.61  thf('20', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.42/0.61  thf(t69_enumset1, axiom,
% 0.42/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.61  thf('21', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.61  thf(t73_zfmisc_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.42/0.61         ((r2_hidden @ X37 @ X38)
% 0.42/0.61          | ((k4_xboole_0 @ (k2_tarski @ X37 @ X39) @ X38) != (k1_xboole_0)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))
% 0.42/0.61          | (r2_hidden @ X0 @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k1_tarski @ X0) != (k1_xboole_0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['20', '23'])).
% 0.42/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.61  thf('25', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.42/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X0 : $i, X2 : $i]:
% 0.42/0.61         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.42/0.61  thf(t64_zfmisc_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.42/0.61       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.42/0.61         (((X33) != (X35))
% 0.42/0.61          | ~ (r2_hidden @ X33 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X35))))),
% 0.42/0.61      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      (![X34 : $i, X35 : $i]:
% 0.42/0.61         ~ (r2_hidden @ X35 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X35)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['28'])).
% 0.42/0.61  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.42/0.61      inference('sup-', [status(thm)], ['27', '29'])).
% 0.42/0.61  thf('31', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.42/0.61      inference('clc', [status(thm)], ['24', '30'])).
% 0.42/0.61  thf('32', plain, ((zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.42/0.61      inference('simplify_reflect-', [status(thm)], ['19', '31'])).
% 0.42/0.61  thf('33', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.42/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.42/0.61         (((k1_relset_1 @ X59 @ X60 @ X58) = (k1_relat_1 @ X58))
% 0.42/0.61          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60))))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)
% 0.42/0.61         = (k1_relat_1 @ sk_D_2))),
% 0.42/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.61  thf('36', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.42/0.61      inference('demod', [status(thm)], ['14', '32', '35'])).
% 0.42/0.61  thf(d5_funct_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( r2_hidden @ C @ B ) <=>
% 0.42/0.61               ( ?[D:$i]:
% 0.42/0.61                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.42/0.61                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.42/0.61  thf('37', plain,
% 0.42/0.61      (![X44 : $i, X46 : $i, X48 : $i, X49 : $i]:
% 0.42/0.61         (((X46) != (k2_relat_1 @ X44))
% 0.42/0.61          | (r2_hidden @ X48 @ X46)
% 0.42/0.61          | ~ (r2_hidden @ X49 @ (k1_relat_1 @ X44))
% 0.42/0.61          | ((X48) != (k1_funct_1 @ X44 @ X49))
% 0.42/0.61          | ~ (v1_funct_1 @ X44)
% 0.42/0.61          | ~ (v1_relat_1 @ X44))),
% 0.42/0.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (![X44 : $i, X49 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X44)
% 0.42/0.61          | ~ (v1_funct_1 @ X44)
% 0.42/0.61          | ~ (r2_hidden @ X49 @ (k1_relat_1 @ X44))
% 0.42/0.61          | (r2_hidden @ (k1_funct_1 @ X44 @ X49) @ (k2_relat_1 @ X44)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['37'])).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.61          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_D_2)
% 0.42/0.61          | ~ (v1_relat_1 @ sk_D_2))),
% 0.42/0.61      inference('sup-', [status(thm)], ['36', '38'])).
% 0.42/0.61  thf('40', plain, ((v1_funct_1 @ sk_D_2)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('41', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf('42', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.61          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.42/0.61      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k2_relat_1 @ sk_D_2))),
% 0.42/0.61      inference('sup-', [status(thm)], ['11', '42'])).
% 0.42/0.61  thf('44', plain,
% 0.42/0.61      (![X33 : $i, X34 : $i, X36 : $i]:
% 0.42/0.61         ((r2_hidden @ X33 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X36)))
% 0.42/0.61          | ((X33) = (X36))
% 0.42/0.61          | ~ (r2_hidden @ X33 @ X34))),
% 0.42/0.61      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k1_funct_1 @ sk_D_2 @ sk_C_1) = (X0))
% 0.42/0.61          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ 
% 0.42/0.61             (k4_xboole_0 @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ X0))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      (((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ k1_xboole_0)
% 0.42/0.61        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['10', '45'])).
% 0.42/0.61  thf('47', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (sk_B))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('48', plain,
% 0.42/0.61      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ k1_xboole_0)),
% 0.42/0.61      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.42/0.61  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.42/0.61      inference('sup-', [status(thm)], ['27', '29'])).
% 0.42/0.61  thf('50', plain, ($false), inference('sup-', [status(thm)], ['48', '49'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
