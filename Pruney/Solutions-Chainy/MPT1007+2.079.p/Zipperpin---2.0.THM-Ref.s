%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.raRq84ijCm

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:26 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 152 expanded)
%              Number of leaves         :   38 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  585 (1635 expanded)
%              Number of equality atoms :   40 ( 100 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_C_2 @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('17',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['14','18'])).

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

thf('20',plain,(
    ! [X24: $i,X26: $i,X28: $i,X29: $i] :
      ( ( X26
       != ( k2_relat_1 @ X24 ) )
      | ( r2_hidden @ X28 @ X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X24 ) )
      | ( X28
       != ( k1_funct_1 @ X24 @ X29 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('21',plain,(
    ! [X24: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X24 @ X29 ) @ ( k2_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X30 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('34',plain,(
    m1_subset_1 @ ( k2_relset_1 @ ( k1_relat_1 @ sk_C_2 ) @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('39',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_2 ) @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','39'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['29','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.raRq84ijCm
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 251 iterations in 0.232s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.69  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.45/0.69  thf(t61_funct_2, conjecture,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.69         ( m1_subset_1 @
% 0.45/0.69           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.69       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.69         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.69        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.69            ( m1_subset_1 @
% 0.45/0.69              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.69          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.69            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.45/0.69  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('1', plain, ((v1_funct_2 @ sk_C_2 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(d1_funct_2, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_1, axiom,
% 0.45/0.69    (![C:$i,B:$i,A:$i]:
% 0.45/0.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.45/0.69         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.45/0.69          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.45/0.69          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.69        | ((k1_tarski @ sk_A)
% 0.45/0.69            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_2)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.69  thf(zf_stmt_2, axiom,
% 0.45/0.69    (![B:$i,A:$i]:
% 0.45/0.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.69       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      (![X39 : $i, X40 : $i]:
% 0.45/0.69         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C_2 @ 
% 0.45/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_5, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.45/0.69         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.45/0.69          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.45/0.69          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.69        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      ((((sk_B) = (k1_xboole_0))
% 0.45/0.69        | (zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['4', '7'])).
% 0.45/0.69  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('10', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A))),
% 0.45/0.69      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C_2 @ 
% 0.45/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.69  thf('12', plain,
% 0.45/0.69      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.69         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.45/0.69          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_2)
% 0.45/0.69         = (k1_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.69  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.45/0.69  thf(t69_enumset1, axiom,
% 0.45/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.69  thf(d2_tarski, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.45/0.69       ( ![D:$i]:
% 0.45/0.69         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.69         (((X5) != (X4))
% 0.45/0.69          | (r2_hidden @ X5 @ X6)
% 0.45/0.69          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.45/0.69      inference('cnf', [status(esa)], [d2_tarski])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.45/0.69      inference('simplify', [status(thm)], ['16'])).
% 0.45/0.69  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['15', '17'])).
% 0.45/0.69  thf('19', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('sup+', [status(thm)], ['14', '18'])).
% 0.45/0.69  thf(d5_funct_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.69               ( ?[D:$i]:
% 0.45/0.69                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.45/0.69                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      (![X24 : $i, X26 : $i, X28 : $i, X29 : $i]:
% 0.45/0.69         (((X26) != (k2_relat_1 @ X24))
% 0.45/0.69          | (r2_hidden @ X28 @ X26)
% 0.45/0.69          | ~ (r2_hidden @ X29 @ (k1_relat_1 @ X24))
% 0.45/0.69          | ((X28) != (k1_funct_1 @ X24 @ X29))
% 0.45/0.69          | ~ (v1_funct_1 @ X24)
% 0.45/0.69          | ~ (v1_relat_1 @ X24))),
% 0.45/0.69      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X24 : $i, X29 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X24)
% 0.45/0.69          | ~ (v1_funct_1 @ X24)
% 0.45/0.69          | ~ (r2_hidden @ X29 @ (k1_relat_1 @ X24))
% 0.45/0.69          | (r2_hidden @ (k1_funct_1 @ X24 @ X29) @ (k2_relat_1 @ X24)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['20'])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      (((r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ (k2_relat_1 @ sk_C_2))
% 0.45/0.69        | ~ (v1_funct_1 @ sk_C_2)
% 0.45/0.69        | ~ (v1_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['19', '21'])).
% 0.45/0.69  thf('23', plain, ((v1_funct_1 @ sk_C_2)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('24', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C_2 @ 
% 0.45/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(cc2_relat_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ A ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.69  thf('25', plain,
% 0.45/0.69      (![X19 : $i, X20 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.45/0.69          | (v1_relat_1 @ X19)
% 0.45/0.69          | ~ (v1_relat_1 @ X20))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.45/0.69        | (v1_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.69  thf(fc6_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.69  thf('28', plain, ((v1_relat_1 @ sk_C_2)),
% 0.45/0.69      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ (k2_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('demod', [status(thm)], ['22', '23', '28'])).
% 0.45/0.69  thf('30', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C_2 @ 
% 0.45/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('31', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C_2 @ 
% 0.45/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ sk_B)))),
% 0.45/0.69      inference('demod', [status(thm)], ['30', '31'])).
% 0.45/0.69  thf(dt_k2_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.69         ((m1_subset_1 @ (k2_relset_1 @ X30 @ X31 @ X32) @ (k1_zfmisc_1 @ X31))
% 0.45/0.69          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.45/0.69  thf('34', plain,
% 0.45/0.69      ((m1_subset_1 @ (k2_relset_1 @ (k1_relat_1 @ sk_C_2) @ sk_B @ sk_C_2) @ 
% 0.45/0.69        (k1_zfmisc_1 @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.69  thf('35', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C_2 @ 
% 0.45/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.69         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 0.45/0.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_2)
% 0.45/0.69         = (k2_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.45/0.69  thf('39', plain,
% 0.45/0.69      (((k2_relset_1 @ (k1_relat_1 @ sk_C_2) @ sk_B @ sk_C_2)
% 0.45/0.69         = (k2_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('demod', [status(thm)], ['37', '38'])).
% 0.45/0.69  thf('40', plain,
% 0.45/0.69      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.45/0.69      inference('demod', [status(thm)], ['34', '39'])).
% 0.45/0.69  thf(t3_subset, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      (![X16 : $i, X17 : $i]:
% 0.45/0.69         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.69  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.45/0.69      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.69  thf(d3_tarski, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.69  thf('43', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.69          | (r2_hidden @ X0 @ X2)
% 0.45/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf('44', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.69  thf('45', plain, ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ sk_B)),
% 0.45/0.69      inference('sup-', [status(thm)], ['29', '44'])).
% 0.45/0.69  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
