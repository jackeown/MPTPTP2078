%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6NwvCDcYOz

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:11 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 205 expanded)
%              Number of leaves         :   41 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  607 (2472 expanded)
%              Number of equality atoms :   47 ( 133 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X15 @ X16 ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

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

thf('1',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('20',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k11_relat_1 @ X19 @ X18 )
        = ( k1_tarski @ ( k1_funct_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X17: $i] :
      ( ( ( k9_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k11_relat_1 @ X11 @ X12 )
        = ( k9_relat_1 @ X11 @ ( k1_tarski @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k2_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['27','28'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['27','28'])).

thf('38',plain,
    ( ( k11_relat_1 @ sk_D_1 @ sk_A )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','29','30','38'])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['16','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k7_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k9_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,(
    ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['27','28'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6NwvCDcYOz
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 114 iterations in 0.111s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.39/0.57  thf(t144_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      (![X15 : $i, X16 : $i]:
% 0.39/0.57         ((r1_tarski @ (k9_relat_1 @ X15 @ X16) @ (k2_relat_1 @ X15))
% 0.39/0.57          | ~ (v1_relat_1 @ X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.39/0.57  thf(t64_funct_2, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.57       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.57         ( r1_tarski @
% 0.39/0.57           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.39/0.57           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.57            ( m1_subset_1 @
% 0.39/0.57              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.57          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.57            ( r1_tarski @
% 0.39/0.57              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.39/0.57              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (~ (r1_tarski @ 
% 0.39/0.57          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.39/0.57          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('2', plain, ((v1_funct_2 @ sk_D_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d1_funct_2, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_1, axiom,
% 0.39/0.57    (![C:$i,B:$i,A:$i]:
% 0.39/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.57         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.39/0.57          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.39/0.57          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.39/0.57        | ((k1_tarski @ sk_A)
% 0.39/0.57            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.57  thf(zf_stmt_2, axiom,
% 0.39/0.57    (![B:$i,A:$i]:
% 0.39/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X27 : $i, X28 : $i]:
% 0.39/0.57         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_5, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.57         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.39/0.57          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.39/0.57          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.39/0.57        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      ((((sk_B) = (k1_xboole_0))
% 0.39/0.57        | (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.39/0.57  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('11', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.57         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.39/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)
% 0.39/0.57         = (k1_relat_1 @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('15', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (~ (r1_tarski @ 
% 0.39/0.57          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.39/0.57          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '15'])).
% 0.39/0.57  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.39/0.57  thf(t69_enumset1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.57  thf('18', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.57  thf(d2_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.39/0.57       ( ![D:$i]:
% 0.39/0.57         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         (((X1) != (X0))
% 0.39/0.57          | (r2_hidden @ X1 @ X2)
% 0.39/0.57          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_tarski])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.57  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['18', '20'])).
% 0.39/0.57  thf('22', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['17', '21'])).
% 0.39/0.57  thf(t117_funct_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.57       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.57         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X18 : $i, X19 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.39/0.57          | ((k11_relat_1 @ X19 @ X18) = (k1_tarski @ (k1_funct_1 @ X19 @ X18)))
% 0.39/0.57          | ~ (v1_funct_1 @ X19)
% 0.39/0.57          | ~ (v1_relat_1 @ X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ sk_D_1)
% 0.39/0.57        | ~ (v1_funct_1 @ sk_D_1)
% 0.39/0.57        | ((k11_relat_1 @ sk_D_1 @ sk_A)
% 0.39/0.57            = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc2_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.39/0.57          | (v1_relat_1 @ X9)
% 0.39/0.57          | ~ (v1_relat_1 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.39/0.57        | (v1_relat_1 @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.57  thf(fc6_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.57  thf('29', plain, ((v1_relat_1 @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.57  thf('30', plain, ((v1_funct_1 @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t146_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (![X17 : $i]:
% 0.39/0.57         (((k9_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (k2_relat_1 @ X17))
% 0.39/0.57          | ~ (v1_relat_1 @ X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.39/0.57  thf('32', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.39/0.57  thf(d16_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i]:
% 0.39/0.57         (((k11_relat_1 @ X11 @ X12) = (k9_relat_1 @ X11 @ (k1_tarski @ X12)))
% 0.39/0.57          | ~ (v1_relat_1 @ X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k11_relat_1 @ X0 @ sk_A)
% 0.39/0.57            = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D_1)))
% 0.39/0.57          | ~ (v1_relat_1 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['32', '33'])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      ((((k11_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_D_1)
% 0.39/0.57        | ~ (v1_relat_1 @ sk_D_1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['31', '34'])).
% 0.39/0.57  thf('36', plain, ((v1_relat_1 @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.57  thf('37', plain, ((v1_relat_1 @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.57  thf('38', plain, (((k11_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['24', '29', '30', '38'])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (~ (r1_tarski @ 
% 0.39/0.57          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.39/0.57          (k2_relat_1 @ sk_D_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['16', '39'])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('42', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)))),
% 0.39/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.39/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.39/0.57          | ((k7_relset_1 @ X24 @ X25 @ X23 @ X26) = (k9_relat_1 @ X23 @ X26)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ X0)
% 0.39/0.57           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['40', '45'])).
% 0.39/0.57  thf('47', plain, (~ (v1_relat_1 @ sk_D_1)),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '46'])).
% 0.39/0.57  thf('48', plain, ((v1_relat_1 @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.57  thf('49', plain, ($false), inference('demod', [status(thm)], ['47', '48'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
