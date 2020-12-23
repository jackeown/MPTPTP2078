%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QX3zmNbHjj

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:24 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 132 expanded)
%              Number of leaves         :   40 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  547 ( 982 expanded)
%              Number of equality atoms :   38 (  60 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t169_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( ( k1_relat_1 @ C )
            = A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
         => ( ( ( k1_relat_1 @ C )
              = A )
            & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( r2_hidden @ X29 @ ( k1_funct_2 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('2',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( r2_hidden @ X29 @ ( k1_funct_2 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf('14',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('31',plain,(
    ! [X19: $i] :
      ( zip_tseitin_0 @ X19 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( zip_tseitin_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,(
    zip_tseitin_0 @ sk_B_1 @ sk_A ),
    inference(eq_fact,[status(thm)],['33'])).

thf('35',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['9','34'])).

thf('36',plain,
    ( sk_A
    = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('51',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('53',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['42','53'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QX3zmNbHjj
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 218 iterations in 0.212s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.67  thf(t169_funct_2, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.67       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.46/0.67         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.46/0.67           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.67        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.67          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.46/0.67            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.46/0.67              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.46/0.67  thf('0', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t121_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.46/0.67       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.67         ((v1_funct_2 @ X29 @ X30 @ X31)
% 0.46/0.67          | ~ (r2_hidden @ X29 @ (k1_funct_2 @ X30 @ X31)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.46/0.67  thf('2', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.67  thf(d1_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_1, axiom,
% 0.46/0.67    (![C:$i,B:$i,A:$i]:
% 0.46/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.67         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.46/0.67          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.46/0.67          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.46/0.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('5', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.67         ((m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.46/0.67          | ~ (r2_hidden @ X29 @ (k1_funct_2 @ X30 @ X31)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.67  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.67  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.67  thf(zf_stmt_4, axiom,
% 0.46/0.67    (![B:$i,A:$i]:
% 0.46/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.67  thf(zf_stmt_5, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.67         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.46/0.67          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.46/0.67          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.46/0.67        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i]:
% 0.46/0.67         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.46/0.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.67  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.46/0.67      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.67  thf(fc3_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.46/0.67       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      (![X27 : $i, X28 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ X27)
% 0.46/0.67          | ~ (v1_xboole_0 @ X28)
% 0.46/0.67          | (v1_xboole_0 @ (k1_funct_2 @ X27 @ X28)))),
% 0.46/0.67      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.46/0.67  thf('14', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(d1_xboole_0, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.67  thf('16', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.67  thf('17', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['13', '16'])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['12', '17'])).
% 0.46/0.67  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.67  thf(d3_tarski, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      (![X6 : $i, X8 : $i]:
% 0.46/0.67         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.67  thf(t12_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      (![X9 : $i, X10 : $i]:
% 0.46/0.67         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.46/0.67      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.67  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['19', '24'])).
% 0.46/0.67  thf(commutativity_k2_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.67  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.67  thf('28', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i]:
% 0.46/0.67         ((zip_tseitin_0 @ X19 @ X20) | ((X20) != (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.46/0.67  thf('31', plain, (![X19 : $i]: (zip_tseitin_0 @ X19 @ k1_xboole_0)),
% 0.46/0.67      inference('simplify', [status(thm)], ['30'])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['29', '31'])).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((zip_tseitin_0 @ sk_B_1 @ X1) | (zip_tseitin_0 @ X0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '32'])).
% 0.46/0.67  thf('34', plain, ((zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.46/0.67      inference('eq_fact', [status(thm)], ['33'])).
% 0.46/0.67  thf('35', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.46/0.67      inference('demod', [status(thm)], ['9', '34'])).
% 0.46/0.67  thf('36', plain, (((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['4', '35'])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.67         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.46/0.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.67  thf('40', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.46/0.67      inference('sup+', [status(thm)], ['36', '39'])).
% 0.46/0.67  thf('41', plain,
% 0.46/0.67      ((((k1_relat_1 @ sk_C_1) != (sk_A))
% 0.46/0.67        | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('42', plain,
% 0.46/0.67      ((((k1_relat_1 @ sk_C_1) != (sk_A)))
% 0.46/0.67         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.46/0.67      inference('split', [status(esa)], ['41'])).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.67  thf(cc2_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.67  thf('44', plain,
% 0.46/0.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.67         ((v5_relat_1 @ X13 @ X15)
% 0.46/0.67          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.67  thf('45', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.46/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.67  thf(d19_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ B ) =>
% 0.46/0.67       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      (![X11 : $i, X12 : $i]:
% 0.46/0.67         (~ (v5_relat_1 @ X11 @ X12)
% 0.46/0.67          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.46/0.67          | ~ (v1_relat_1 @ X11))),
% 0.46/0.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.67  thf('47', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.67  thf('48', plain, ((v1_relat_1 @ sk_C_1)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('49', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.46/0.67      inference('demod', [status(thm)], ['47', '48'])).
% 0.46/0.67  thf('50', plain,
% 0.46/0.67      ((~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))
% 0.46/0.67         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.46/0.67      inference('split', [status(esa)], ['41'])).
% 0.46/0.67  thf('51', plain, (((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.67  thf('52', plain,
% 0.46/0.67      (~ (((k1_relat_1 @ sk_C_1) = (sk_A))) | 
% 0.46/0.67       ~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.46/0.67      inference('split', [status(esa)], ['41'])).
% 0.46/0.67  thf('53', plain, (~ (((k1_relat_1 @ sk_C_1) = (sk_A)))),
% 0.46/0.67      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.46/0.67  thf('54', plain, (((k1_relat_1 @ sk_C_1) != (sk_A))),
% 0.46/0.67      inference('simpl_trail', [status(thm)], ['42', '53'])).
% 0.46/0.67  thf('55', plain, ($false),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['40', '54'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
