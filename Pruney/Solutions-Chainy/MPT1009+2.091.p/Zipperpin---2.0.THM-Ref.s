%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eBLfLMEw4G

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:01 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 156 expanded)
%              Number of leaves         :   36 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  610 (1929 expanded)
%              Number of equality atoms :   44 ( 113 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
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

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('10',plain,(
    v1_funct_2 @ sk_D_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('11',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('15',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','19','22'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X24 ) )
      | ( ( k9_relat_1 @ X24 @ ( k2_tarski @ X23 @ X25 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X24 @ X23 ) @ ( k1_funct_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ X0 @ X1 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_funct_1 @ sk_D_1 @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','19','22'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ X0 @ X1 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_funct_1 @ sk_D_1 @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','31'])).

thf('33',plain,
    ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','32'])).

thf('34',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,
    ( ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','19','22'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ X22 ) @ ( k9_relat_1 @ X21 @ ( k1_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['4','36','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eBLfLMEw4G
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 137 iterations in 0.278s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.54/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.54/0.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.74  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.54/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.54/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.74  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.54/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.54/0.74  thf(t64_funct_2, conjecture,
% 0.54/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.54/0.74         ( m1_subset_1 @
% 0.54/0.74           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.54/0.74       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.54/0.74         ( r1_tarski @
% 0.54/0.74           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.54/0.74           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.74        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.54/0.74            ( m1_subset_1 @
% 0.54/0.74              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.54/0.74          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.54/0.74            ( r1_tarski @
% 0.54/0.74              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.54/0.74              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.54/0.74    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.54/0.74  thf('0', plain,
% 0.54/0.74      (~ (r1_tarski @ 
% 0.54/0.74          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C_1) @ 
% 0.54/0.74          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('1', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_D_1 @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(redefinition_k7_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.54/0.74  thf('2', plain,
% 0.54/0.74      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.54/0.74          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.54/0.74  thf('3', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.54/0.74           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.74  thf('4', plain,
% 0.54/0.74      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_1) @ 
% 0.54/0.74          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.74  thf(t69_enumset1, axiom,
% 0.54/0.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.74  thf('5', plain, (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.54/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.74  thf(d2_tarski, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.54/0.74       ( ![D:$i]:
% 0.54/0.74         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.54/0.74  thf('6', plain,
% 0.54/0.74      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.54/0.74         (((X5) != (X4))
% 0.54/0.74          | (r2_hidden @ X5 @ X6)
% 0.54/0.74          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.54/0.74      inference('cnf', [status(esa)], [d2_tarski])).
% 0.54/0.74  thf('7', plain,
% 0.54/0.74      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.54/0.74      inference('simplify', [status(thm)], ['6'])).
% 0.54/0.74  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['5', '7'])).
% 0.54/0.74  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['5', '7'])).
% 0.54/0.74  thf('10', plain, ((v1_funct_2 @ sk_D_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(d1_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.54/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.54/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.54/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_1, axiom,
% 0.54/0.74    (![C:$i,B:$i,A:$i]:
% 0.54/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.54/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.54/0.74  thf('11', plain,
% 0.54/0.74      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.54/0.74         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.54/0.74          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.54/0.74          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.74  thf('12', plain,
% 0.54/0.74      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.54/0.74        | ((k1_tarski @ sk_A)
% 0.54/0.74            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.74  thf(zf_stmt_2, axiom,
% 0.54/0.74    (![B:$i,A:$i]:
% 0.54/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.74       ( zip_tseitin_0 @ B @ A ) ))).
% 0.54/0.74  thf('13', plain,
% 0.54/0.74      (![X36 : $i, X37 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.74  thf('14', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_D_1 @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_5, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.54/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.54/0.74  thf('15', plain,
% 0.54/0.74      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.54/0.74         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.54/0.74          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.54/0.74          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.74  thf('16', plain,
% 0.54/0.74      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.54/0.74        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.74  thf('17', plain,
% 0.54/0.74      ((((sk_B) = (k1_xboole_0))
% 0.54/0.74        | (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['13', '16'])).
% 0.54/0.74  thf('18', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('19', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.54/0.74      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.54/0.74  thf('20', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_D_1 @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.74  thf('21', plain,
% 0.54/0.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.54/0.74         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.54/0.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.74  thf('22', plain,
% 0.54/0.74      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)
% 0.54/0.74         = (k1_relat_1 @ sk_D_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.74  thf('23', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['12', '19', '22'])).
% 0.54/0.74  thf(t118_funct_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.54/0.74       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.54/0.74           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.54/0.74         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.54/0.74           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.54/0.74  thf('24', plain,
% 0.54/0.74      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.54/0.74         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.54/0.74          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X24))
% 0.54/0.74          | ((k9_relat_1 @ X24 @ (k2_tarski @ X23 @ X25))
% 0.54/0.74              = (k2_tarski @ (k1_funct_1 @ X24 @ X23) @ 
% 0.54/0.74                 (k1_funct_1 @ X24 @ X25)))
% 0.54/0.74          | ~ (v1_funct_1 @ X24)
% 0.54/0.74          | ~ (v1_relat_1 @ X24))),
% 0.54/0.74      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.54/0.74  thf('25', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.54/0.74          | ~ (v1_relat_1 @ sk_D_1)
% 0.54/0.74          | ~ (v1_funct_1 @ sk_D_1)
% 0.54/0.74          | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ X0 @ X1))
% 0.54/0.74              = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ X0) @ 
% 0.54/0.74                 (k1_funct_1 @ sk_D_1 @ X1)))
% 0.54/0.74          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_D_1)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.74  thf('26', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_D_1 @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(cc1_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( v1_relat_1 @ C ) ))).
% 0.54/0.74  thf('27', plain,
% 0.54/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.74         ((v1_relat_1 @ X26)
% 0.54/0.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.74  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.54/0.74      inference('sup-', [status(thm)], ['26', '27'])).
% 0.54/0.74  thf('29', plain, ((v1_funct_1 @ sk_D_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('30', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['12', '19', '22'])).
% 0.54/0.74  thf('31', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.54/0.74          | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ X0 @ X1))
% 0.54/0.74              = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ X0) @ 
% 0.54/0.74                 (k1_funct_1 @ sk_D_1 @ X1)))
% 0.54/0.74          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['25', '28', '29', '30'])).
% 0.54/0.74  thf('32', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.54/0.74          | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ X0))
% 0.54/0.74              = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.54/0.74                 (k1_funct_1 @ sk_D_1 @ X0))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['9', '31'])).
% 0.54/0.74  thf('33', plain,
% 0.54/0.74      (((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ sk_A))
% 0.54/0.74         = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.54/0.74            (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['8', '32'])).
% 0.54/0.74  thf('34', plain,
% 0.54/0.74      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.54/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.74  thf('35', plain,
% 0.54/0.74      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.54/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.74  thf('36', plain,
% 0.54/0.74      (((k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))
% 0.54/0.74         = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.54/0.74  thf('37', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['12', '19', '22'])).
% 0.54/0.74  thf(t147_relat_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ B ) =>
% 0.54/0.74       ( r1_tarski @
% 0.54/0.74         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.54/0.74  thf('38', plain,
% 0.54/0.74      (![X21 : $i, X22 : $i]:
% 0.54/0.74         ((r1_tarski @ (k9_relat_1 @ X21 @ X22) @ 
% 0.54/0.74           (k9_relat_1 @ X21 @ (k1_relat_1 @ X21)))
% 0.54/0.74          | ~ (v1_relat_1 @ X21))),
% 0.54/0.74      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.54/0.74  thf('39', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((r1_tarski @ (k9_relat_1 @ sk_D_1 @ X0) @ 
% 0.54/0.74           (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))
% 0.54/0.74          | ~ (v1_relat_1 @ sk_D_1))),
% 0.54/0.74      inference('sup+', [status(thm)], ['37', '38'])).
% 0.54/0.74  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 0.54/0.74      inference('sup-', [status(thm)], ['26', '27'])).
% 0.54/0.74  thf('41', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (r1_tarski @ (k9_relat_1 @ sk_D_1 @ X0) @ 
% 0.54/0.74          (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['39', '40'])).
% 0.54/0.74  thf('42', plain, ($false),
% 0.54/0.74      inference('demod', [status(thm)], ['4', '36', '41'])).
% 0.54/0.74  
% 0.54/0.74  % SZS output end Refutation
% 0.54/0.74  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
