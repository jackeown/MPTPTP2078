%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mwXKJ01FY8

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 110 expanded)
%              Number of leaves         :   40 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  634 (1006 expanded)
%              Number of equality atoms :   46 (  66 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ ( k1_tarski @ sk_B ) ),
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

thf('2',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('5',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('12',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['3','17','20'])).

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

thf('22',plain,(
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

thf('23',plain,(
    ! [X21: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X21 @ X26 ) @ ( k2_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['24','25','28'])).

thf('30',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['0','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X32 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('33',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ( X9 = X8 )
      | ( X9 = X5 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('45',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X9 = X5 )
      | ( X9 = X8 )
      | ~ ( r2_hidden @ X9 @ ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k1_funct_1 @ sk_D_3 @ sk_C_2 )
    = sk_B ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ( k1_funct_1 @ sk_D_3 @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mwXKJ01FY8
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.60  % Solved by: fo/fo7.sh
% 0.21/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.60  % done 232 iterations in 0.147s
% 0.21/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.60  % SZS output start Refutation
% 0.21/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.60  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.21/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.60  thf(t65_funct_2, conjecture,
% 0.21/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.60         ( m1_subset_1 @
% 0.21/0.60           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.60       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.60            ( m1_subset_1 @
% 0.21/0.60              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.60          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.21/0.60  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('1', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(d1_funct_2, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_1, axiom,
% 0.21/0.60    (![C:$i,B:$i,A:$i]:
% 0.21/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.21/0.60         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.21/0.60          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 0.21/0.60          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.60  thf('3', plain,
% 0.21/0.60      ((~ (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)
% 0.21/0.60        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.60  thf('4', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_D_3 @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.60  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.60  thf(zf_stmt_4, axiom,
% 0.21/0.60    (![B:$i,A:$i]:
% 0.21/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.60  thf(zf_stmt_5, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.60  thf('5', plain,
% 0.21/0.60      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.21/0.60         (~ (zip_tseitin_0 @ X46 @ X47)
% 0.21/0.60          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 0.21/0.60          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.60  thf('6', plain,
% 0.21/0.60      (((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)
% 0.21/0.60        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.60  thf('7', plain,
% 0.21/0.60      (![X41 : $i, X42 : $i]:
% 0.21/0.60         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.60  thf('8', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.60  thf('9', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.21/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.60  thf(t69_enumset1, axiom,
% 0.21/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.60  thf('10', plain,
% 0.21/0.60      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.21/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.60  thf(d2_tarski, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.60       ( ![D:$i]:
% 0.21/0.60         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.60  thf('11', plain,
% 0.21/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.60         (((X6) != (X5))
% 0.21/0.60          | (r2_hidden @ X6 @ X7)
% 0.21/0.60          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.21/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.60  thf('12', plain,
% 0.21/0.60      (![X5 : $i, X8 : $i]: (r2_hidden @ X5 @ (k2_tarski @ X8 @ X5))),
% 0.21/0.60      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.60  thf(t7_ordinal1, axiom,
% 0.21/0.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.60  thf('13', plain,
% 0.21/0.60      (![X27 : $i, X28 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.60  thf('14', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]: ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X0)),
% 0.21/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.60  thf('15', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.21/0.60      inference('sup-', [status(thm)], ['10', '14'])).
% 0.21/0.60  thf('16', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]: (zip_tseitin_0 @ (k1_tarski @ X0) @ X1)),
% 0.21/0.60      inference('sup-', [status(thm)], ['9', '15'])).
% 0.21/0.60  thf('17', plain, ((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.60      inference('demod', [status(thm)], ['6', '16'])).
% 0.21/0.60  thf('18', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_D_3 @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.60  thf('19', plain,
% 0.21/0.60      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.60         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.21/0.60          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.21/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.60  thf('20', plain,
% 0.21/0.60      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3)
% 0.21/0.60         = (k1_relat_1 @ sk_D_3))),
% 0.21/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.60  thf('21', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 0.21/0.60      inference('demod', [status(thm)], ['3', '17', '20'])).
% 0.21/0.60  thf(d5_funct_1, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.60           ( ![C:$i]:
% 0.21/0.60             ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.60               ( ?[D:$i]:
% 0.21/0.60                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.60                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.60  thf('22', plain,
% 0.21/0.60      (![X21 : $i, X23 : $i, X25 : $i, X26 : $i]:
% 0.21/0.60         (((X23) != (k2_relat_1 @ X21))
% 0.21/0.60          | (r2_hidden @ X25 @ X23)
% 0.21/0.60          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X21))
% 0.21/0.60          | ((X25) != (k1_funct_1 @ X21 @ X26))
% 0.21/0.60          | ~ (v1_funct_1 @ X21)
% 0.21/0.60          | ~ (v1_relat_1 @ X21))),
% 0.21/0.60      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.21/0.60  thf('23', plain,
% 0.21/0.60      (![X21 : $i, X26 : $i]:
% 0.21/0.60         (~ (v1_relat_1 @ X21)
% 0.21/0.60          | ~ (v1_funct_1 @ X21)
% 0.21/0.60          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X21))
% 0.21/0.60          | (r2_hidden @ (k1_funct_1 @ X21 @ X26) @ (k2_relat_1 @ X21)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.60  thf('24', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.60          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3))
% 0.21/0.60          | ~ (v1_funct_1 @ sk_D_3)
% 0.21/0.60          | ~ (v1_relat_1 @ sk_D_3))),
% 0.21/0.60      inference('sup-', [status(thm)], ['21', '23'])).
% 0.21/0.60  thf('25', plain, ((v1_funct_1 @ sk_D_3)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('26', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_D_3 @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(cc1_relset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( v1_relat_1 @ C ) ))).
% 0.21/0.60  thf('27', plain,
% 0.21/0.60      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.60         ((v1_relat_1 @ X29)
% 0.21/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.21/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.60  thf('28', plain, ((v1_relat_1 @ sk_D_3)),
% 0.21/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.60  thf('29', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.60          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3)))),
% 0.21/0.60      inference('demod', [status(thm)], ['24', '25', '28'])).
% 0.21/0.60  thf('30', plain,
% 0.21/0.60      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_2) @ (k2_relat_1 @ sk_D_3))),
% 0.21/0.60      inference('sup-', [status(thm)], ['0', '29'])).
% 0.21/0.60  thf('31', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_D_3 @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(dt_k2_relset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.60  thf('32', plain,
% 0.21/0.60      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.60         ((m1_subset_1 @ (k2_relset_1 @ X32 @ X33 @ X34) @ (k1_zfmisc_1 @ X33))
% 0.21/0.60          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.21/0.60  thf('33', plain,
% 0.21/0.60      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3) @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.60  thf('34', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_D_3 @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.60  thf('35', plain,
% 0.21/0.60      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.21/0.60         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 0.21/0.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.21/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.60  thf('36', plain,
% 0.21/0.60      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3)
% 0.21/0.60         = (k2_relat_1 @ sk_D_3))),
% 0.21/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.60  thf('37', plain,
% 0.21/0.60      ((m1_subset_1 @ (k2_relat_1 @ sk_D_3) @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.21/0.60      inference('demod', [status(thm)], ['33', '36'])).
% 0.21/0.60  thf(t3_subset, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.60  thf('38', plain,
% 0.21/0.60      (![X17 : $i, X18 : $i]:
% 0.21/0.60         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.60  thf('39', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_3) @ (k1_tarski @ sk_B))),
% 0.21/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.60  thf(d3_tarski, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.60  thf('40', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.60          | (r2_hidden @ X0 @ X2)
% 0.21/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.60  thf('41', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.21/0.60          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.60  thf('42', plain,
% 0.21/0.60      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_2) @ (k1_tarski @ sk_B))),
% 0.21/0.60      inference('sup-', [status(thm)], ['30', '41'])).
% 0.21/0.60  thf('43', plain,
% 0.21/0.60      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.21/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.60  thf('44', plain,
% 0.21/0.60      (![X5 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X9 @ X7)
% 0.21/0.60          | ((X9) = (X8))
% 0.21/0.60          | ((X9) = (X5))
% 0.21/0.60          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.21/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.60  thf('45', plain,
% 0.21/0.60      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.21/0.60         (((X9) = (X5))
% 0.21/0.60          | ((X9) = (X8))
% 0.21/0.60          | ~ (r2_hidden @ X9 @ (k2_tarski @ X8 @ X5)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.60  thf('46', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['43', '45'])).
% 0.21/0.60  thf('47', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.60  thf('48', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_2) = (sk_B))),
% 0.21/0.60      inference('sup-', [status(thm)], ['42', '47'])).
% 0.21/0.60  thf('49', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_2) != (sk_B))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('50', plain, ($false),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.21/0.60  
% 0.21/0.60  % SZS output end Refutation
% 0.21/0.60  
% 0.46/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
