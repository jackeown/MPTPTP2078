%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GAFGkd7Lly

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:21 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 114 expanded)
%              Number of leaves         :   39 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  688 (1076 expanded)
%              Number of equality atoms :   56 (  77 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('2',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( v1_funct_2 @ X63 @ X61 @ X62 )
      | ( X61
        = ( k1_relset_1 @ X61 @ X62 @ X63 ) )
      | ~ ( zip_tseitin_1 @ X63 @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( zip_tseitin_0 @ X64 @ X65 )
      | ( zip_tseitin_1 @ X66 @ X64 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X64 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X59: $i,X60: $i] :
      ( ( zip_tseitin_0 @ X59 @ X60 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('12',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ X35 )
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k1_relset_1 @ X54 @ X55 @ X53 )
        = ( k1_relat_1 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['3','16','19'])).

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

thf('21',plain,(
    ! [X41: $i,X43: $i,X45: $i,X46: $i] :
      ( ( X43
       != ( k2_relat_1 @ X41 ) )
      | ( r2_hidden @ X45 @ X43 )
      | ~ ( r2_hidden @ X46 @ ( k1_relat_1 @ X41 ) )
      | ( X45
       != ( k1_funct_1 @ X41 @ X46 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('22',plain,(
    ! [X41: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( r2_hidden @ X46 @ ( k1_relat_1 @ X41 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X41 @ X46 ) @ ( k2_relat_1 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v1_relat_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('29',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X34: $i,X36: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ X36 )
        = ( k1_tarski @ X34 ) )
      | ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X50 @ X51 @ X52 ) @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('35',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k2_relset_1 @ X57 @ X58 @ X56 )
        = ( k2_relat_1 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('40',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ( r2_hidden @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( X4 = X1 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('44',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
        = ( k1_tarski @ X0 ) )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('47',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ X35 )
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) )
      | ( X0 = sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C_2 )
    = sk_B ),
    inference('sup-',[status(thm)],['29','50'])).

thf('52',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GAFGkd7Lly
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 171 iterations in 0.140s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.38/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.59  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.38/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.59  thf(t65_funct_2, conjecture,
% 0.38/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.38/0.59         ( m1_subset_1 @
% 0.38/0.59           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.38/0.59       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.59        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.38/0.59            ( m1_subset_1 @
% 0.38/0.59              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.38/0.59          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.38/0.59  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('1', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(d1_funct_2, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_1, axiom,
% 0.38/0.59    (![C:$i,B:$i,A:$i]:
% 0.38/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.38/0.59         (~ (v1_funct_2 @ X63 @ X61 @ X62)
% 0.38/0.59          | ((X61) = (k1_relset_1 @ X61 @ X62 @ X63))
% 0.38/0.59          | ~ (zip_tseitin_1 @ X63 @ X62 @ X61))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      ((~ (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.38/0.59        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_D_2 @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.59  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.59  thf(zf_stmt_4, axiom,
% 0.38/0.59    (![B:$i,A:$i]:
% 0.38/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.59  thf(zf_stmt_5, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (![X64 : $i, X65 : $i, X66 : $i]:
% 0.38/0.59         (~ (zip_tseitin_0 @ X64 @ X65)
% 0.38/0.59          | (zip_tseitin_1 @ X66 @ X64 @ X65)
% 0.38/0.59          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X64))))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (((zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.38/0.59        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.59  thf(d1_tarski, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         (((X2) != (X1)) | (r2_hidden @ X2 @ X3) | ((X3) != (k1_tarski @ X1)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.59  thf('8', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.38/0.59      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (![X59 : $i, X60 : $i]:
% 0.38/0.59         ((zip_tseitin_0 @ X59 @ X60) | ((X59) = (k1_xboole_0)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.59  thf(t3_boole, axiom,
% 0.38/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.59  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ X1 @ X0) = (X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.38/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.59  thf(l33_zfmisc_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.59       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (![X34 : $i, X35 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X34 @ X35)
% 0.38/0.59          | ((k4_xboole_0 @ (k1_tarski @ X34) @ X35) != (k1_tarski @ X34)))),
% 0.38/0.59      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.38/0.59          | (zip_tseitin_0 @ X1 @ X2)
% 0.38/0.59          | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X0 @ X1) | (zip_tseitin_0 @ X1 @ X2))),
% 0.38/0.59      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: (zip_tseitin_0 @ (k1_tarski @ X0) @ X1)),
% 0.38/0.59      inference('sup-', [status(thm)], ['8', '14'])).
% 0.38/0.59  thf('16', plain, ((zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.38/0.59      inference('demod', [status(thm)], ['6', '15'])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_D_2 @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.38/0.59         (((k1_relset_1 @ X54 @ X55 @ X53) = (k1_relat_1 @ X53))
% 0.38/0.59          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)
% 0.38/0.59         = (k1_relat_1 @ sk_D_2))),
% 0.38/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.59  thf('20', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '16', '19'])).
% 0.38/0.59  thf(d5_funct_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.59               ( ?[D:$i]:
% 0.38/0.59                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.38/0.59                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (![X41 : $i, X43 : $i, X45 : $i, X46 : $i]:
% 0.38/0.59         (((X43) != (k2_relat_1 @ X41))
% 0.38/0.59          | (r2_hidden @ X45 @ X43)
% 0.38/0.59          | ~ (r2_hidden @ X46 @ (k1_relat_1 @ X41))
% 0.38/0.59          | ((X45) != (k1_funct_1 @ X41 @ X46))
% 0.38/0.59          | ~ (v1_funct_1 @ X41)
% 0.38/0.59          | ~ (v1_relat_1 @ X41))),
% 0.38/0.59      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (![X41 : $i, X46 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X41)
% 0.38/0.59          | ~ (v1_funct_1 @ X41)
% 0.38/0.59          | ~ (r2_hidden @ X46 @ (k1_relat_1 @ X41))
% 0.38/0.59          | (r2_hidden @ (k1_funct_1 @ X41 @ X46) @ (k2_relat_1 @ X41)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['21'])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.38/0.59          | ~ (v1_funct_1 @ sk_D_2)
% 0.38/0.59          | ~ (v1_relat_1 @ sk_D_2))),
% 0.38/0.59      inference('sup-', [status(thm)], ['20', '22'])).
% 0.38/0.59  thf('24', plain, ((v1_funct_1 @ sk_D_2)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_D_2 @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(cc1_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( v1_relat_1 @ C ) ))).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.38/0.59         ((v1_relat_1 @ X47)
% 0.38/0.59          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.59  thf('27', plain, ((v1_relat_1 @ sk_D_2)),
% 0.38/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.38/0.59      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.38/0.59  thf('29', plain,
% 0.38/0.59      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k2_relat_1 @ sk_D_2))),
% 0.38/0.59      inference('sup-', [status(thm)], ['0', '28'])).
% 0.38/0.59  thf(t69_enumset1, axiom,
% 0.38/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.59  thf('30', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      (![X34 : $i, X36 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ (k1_tarski @ X34) @ X36) = (k1_tarski @ X34))
% 0.38/0.59          | (r2_hidden @ X34 @ X36))),
% 0.38/0.59      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) = (k1_tarski @ X0))
% 0.38/0.59          | (r2_hidden @ X0 @ X1))),
% 0.38/0.59      inference('sup+', [status(thm)], ['30', '31'])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_D_2 @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(dt_k2_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.38/0.59  thf('34', plain,
% 0.38/0.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.38/0.59         ((m1_subset_1 @ (k2_relset_1 @ X50 @ X51 @ X52) @ (k1_zfmisc_1 @ X51))
% 0.38/0.59          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51))))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_D_2 @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.59  thf('37', plain,
% 0.38/0.59      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.38/0.59         (((k2_relset_1 @ X57 @ X58 @ X56) = (k2_relat_1 @ X56))
% 0.38/0.59          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.59  thf('38', plain,
% 0.38/0.59      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)
% 0.38/0.59         = (k2_relat_1 @ sk_D_2))),
% 0.38/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.59  thf('39', plain,
% 0.38/0.59      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['35', '38'])).
% 0.38/0.59  thf(l3_subset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X37 @ X38)
% 0.38/0.59          | (r2_hidden @ X37 @ X39)
% 0.38/0.59          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.38/0.59      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.38/0.59            = (k1_tarski @ X0))
% 0.38/0.59          | (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['32', '41'])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X4 @ X3) | ((X4) = (X1)) | ((X3) != (k1_tarski @ X1)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      (![X1 : $i, X4 : $i]:
% 0.38/0.59         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.38/0.59  thf('45', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.38/0.59            = (k1_tarski @ X0))
% 0.38/0.59          | ((X0) = (sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['42', '44'])).
% 0.38/0.59  thf('46', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      (![X34 : $i, X35 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X34 @ X35)
% 0.38/0.59          | ((k4_xboole_0 @ (k1_tarski @ X34) @ X35) != (k1_tarski @ X34)))),
% 0.38/0.59      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.38/0.59  thf('48', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) != (k1_tarski @ X0))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.38/0.59          | ((X0) = (sk_B))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['45', '48'])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)) | ((X0) = (sk_B)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['49'])).
% 0.38/0.59  thf('51', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_2) = (sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['29', '50'])).
% 0.38/0.59  thf('52', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_2) != (sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('53', plain, ($false),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.46/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
