%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B5vXOopMhF

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:15 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 111 expanded)
%              Number of leaves         :   40 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  590 ( 985 expanded)
%              Number of equality atoms :   43 (  63 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ X24 @ X23 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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
    ! [X17: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X19
       != ( k2_relat_1 @ X17 ) )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X17 ) )
      | ( X21
       != ( k1_funct_1 @ X17 @ X22 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('23',plain,(
    ! [X17: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X17 @ X22 ) @ ( k2_relat_1 @ X17 ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('33',plain,(
    v5_relat_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('37',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ( X9 = X8 )
      | ( X9 = X5 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('43',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X9 = X5 )
      | ( X9 = X8 )
      | ~ ( r2_hidden @ X9 @ ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k1_funct_1 @ sk_D_3 @ sk_C_2 )
    = sk_B ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ( k1_funct_1 @ sk_D_3 @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B5vXOopMhF
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.61  % Solved by: fo/fo7.sh
% 0.36/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.61  % done 278 iterations in 0.156s
% 0.36/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.61  % SZS output start Refutation
% 0.36/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.61  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.36/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.36/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.61  thf(t65_funct_2, conjecture,
% 0.36/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.36/0.61         ( m1_subset_1 @
% 0.36/0.61           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.36/0.61       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.36/0.61            ( m1_subset_1 @
% 0.36/0.61              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.36/0.61          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.36/0.61    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.36/0.61  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('1', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ (k1_tarski @ sk_B))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(d1_funct_2, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_1, axiom,
% 0.36/0.61    (![C:$i,B:$i,A:$i]:
% 0.36/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.61  thf('2', plain,
% 0.36/0.61      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.36/0.61         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.36/0.61          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.36/0.61          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.61  thf('3', plain,
% 0.36/0.61      ((~ (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)
% 0.36/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.61  thf('4', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_3 @ 
% 0.36/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.61  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.61  thf(zf_stmt_4, axiom,
% 0.36/0.61    (![B:$i,A:$i]:
% 0.36/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.61  thf(zf_stmt_5, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.61  thf('5', plain,
% 0.36/0.61      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.36/0.61         (~ (zip_tseitin_0 @ X39 @ X40)
% 0.36/0.61          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 0.36/0.61          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.61  thf('6', plain,
% 0.36/0.61      (((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)
% 0.36/0.61        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.61  thf('7', plain,
% 0.36/0.61      (![X34 : $i, X35 : $i]:
% 0.36/0.61         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.61  thf('8', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.36/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.61  thf('9', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.61         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.36/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.36/0.61  thf(t69_enumset1, axiom,
% 0.36/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.61  thf('10', plain,
% 0.36/0.61      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.36/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.61  thf(d2_tarski, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.36/0.61       ( ![D:$i]:
% 0.36/0.61         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.36/0.61  thf('11', plain,
% 0.36/0.61      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.61         (((X6) != (X5))
% 0.36/0.61          | (r2_hidden @ X6 @ X7)
% 0.36/0.61          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_tarski])).
% 0.36/0.61  thf('12', plain,
% 0.36/0.61      (![X5 : $i, X8 : $i]: (r2_hidden @ X5 @ (k2_tarski @ X8 @ X5))),
% 0.36/0.61      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.61  thf(t7_ordinal1, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.61  thf('13', plain,
% 0.36/0.61      (![X23 : $i, X24 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X23 @ X24) | ~ (r1_tarski @ X24 @ X23))),
% 0.36/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.61  thf('14', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X0)),
% 0.36/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.61  thf('15', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.36/0.61      inference('sup-', [status(thm)], ['10', '14'])).
% 0.36/0.61  thf('16', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: (zip_tseitin_0 @ (k1_tarski @ X0) @ X1)),
% 0.36/0.61      inference('sup-', [status(thm)], ['9', '15'])).
% 0.36/0.61  thf('17', plain, ((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.36/0.61      inference('demod', [status(thm)], ['6', '16'])).
% 0.36/0.61  thf('18', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_3 @ 
% 0.36/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.61  thf('19', plain,
% 0.36/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.61         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.36/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.61  thf('20', plain,
% 0.36/0.61      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3)
% 0.36/0.61         = (k1_relat_1 @ sk_D_3))),
% 0.36/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.61  thf('21', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 0.36/0.61      inference('demod', [status(thm)], ['3', '17', '20'])).
% 0.36/0.61  thf(d5_funct_1, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.36/0.61           ( ![C:$i]:
% 0.36/0.61             ( ( r2_hidden @ C @ B ) <=>
% 0.36/0.61               ( ?[D:$i]:
% 0.36/0.61                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.36/0.61                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.36/0.61  thf('22', plain,
% 0.36/0.61      (![X17 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 0.36/0.61         (((X19) != (k2_relat_1 @ X17))
% 0.36/0.61          | (r2_hidden @ X21 @ X19)
% 0.36/0.61          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X17))
% 0.36/0.61          | ((X21) != (k1_funct_1 @ X17 @ X22))
% 0.36/0.61          | ~ (v1_funct_1 @ X17)
% 0.36/0.61          | ~ (v1_relat_1 @ X17))),
% 0.36/0.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.36/0.61  thf('23', plain,
% 0.36/0.61      (![X17 : $i, X22 : $i]:
% 0.36/0.61         (~ (v1_relat_1 @ X17)
% 0.36/0.61          | ~ (v1_funct_1 @ X17)
% 0.36/0.61          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X17))
% 0.36/0.61          | (r2_hidden @ (k1_funct_1 @ X17 @ X22) @ (k2_relat_1 @ X17)))),
% 0.36/0.61      inference('simplify', [status(thm)], ['22'])).
% 0.36/0.61  thf('24', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.61          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3))
% 0.36/0.61          | ~ (v1_funct_1 @ sk_D_3)
% 0.36/0.61          | ~ (v1_relat_1 @ sk_D_3))),
% 0.36/0.61      inference('sup-', [status(thm)], ['21', '23'])).
% 0.36/0.61  thf('25', plain, ((v1_funct_1 @ sk_D_3)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('26', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_3 @ 
% 0.36/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(cc1_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( v1_relat_1 @ C ) ))).
% 0.36/0.61  thf('27', plain,
% 0.36/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.61         ((v1_relat_1 @ X25)
% 0.36/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.36/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.61  thf('28', plain, ((v1_relat_1 @ sk_D_3)),
% 0.36/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.61  thf('29', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.61          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3)))),
% 0.36/0.61      inference('demod', [status(thm)], ['24', '25', '28'])).
% 0.36/0.61  thf('30', plain,
% 0.36/0.61      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_2) @ (k2_relat_1 @ sk_D_3))),
% 0.36/0.61      inference('sup-', [status(thm)], ['0', '29'])).
% 0.36/0.61  thf('31', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_D_3 @ 
% 0.36/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(cc2_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.61  thf('32', plain,
% 0.36/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.61         ((v5_relat_1 @ X28 @ X30)
% 0.36/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.36/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.61  thf('33', plain, ((v5_relat_1 @ sk_D_3 @ (k1_tarski @ sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.61  thf(d19_relat_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( v1_relat_1 @ B ) =>
% 0.36/0.61       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.61  thf('34', plain,
% 0.36/0.61      (![X14 : $i, X15 : $i]:
% 0.36/0.61         (~ (v5_relat_1 @ X14 @ X15)
% 0.36/0.61          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.36/0.61          | ~ (v1_relat_1 @ X14))),
% 0.36/0.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.36/0.61  thf('35', plain,
% 0.36/0.61      ((~ (v1_relat_1 @ sk_D_3)
% 0.36/0.61        | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ (k1_tarski @ sk_B)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.61  thf('36', plain, ((v1_relat_1 @ sk_D_3)),
% 0.36/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.61  thf('37', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_3) @ (k1_tarski @ sk_B))),
% 0.36/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.61  thf(d3_tarski, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.61  thf('38', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.61          | (r2_hidden @ X0 @ X2)
% 0.36/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.61  thf('39', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.36/0.61          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.61  thf('40', plain,
% 0.36/0.61      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_2) @ (k1_tarski @ sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['30', '39'])).
% 0.36/0.61  thf('41', plain,
% 0.36/0.61      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.36/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.61  thf('42', plain,
% 0.36/0.61      (![X5 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X9 @ X7)
% 0.36/0.61          | ((X9) = (X8))
% 0.36/0.61          | ((X9) = (X5))
% 0.36/0.61          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_tarski])).
% 0.36/0.61  thf('43', plain,
% 0.36/0.61      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.36/0.61         (((X9) = (X5))
% 0.36/0.61          | ((X9) = (X8))
% 0.36/0.61          | ~ (r2_hidden @ X9 @ (k2_tarski @ X8 @ X5)))),
% 0.36/0.61      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.61  thf('44', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['41', '43'])).
% 0.36/0.61  thf('45', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.36/0.61      inference('simplify', [status(thm)], ['44'])).
% 0.36/0.61  thf('46', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_2) = (sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['40', '45'])).
% 0.36/0.61  thf('47', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_2) != (sk_B))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('48', plain, ($false),
% 0.36/0.61      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.36/0.61  
% 0.36/0.61  % SZS output end Refutation
% 0.36/0.61  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
