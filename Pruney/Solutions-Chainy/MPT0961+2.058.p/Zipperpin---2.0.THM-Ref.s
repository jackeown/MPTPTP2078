%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qKuqW10Fc5

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:46 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 714 expanded)
%              Number of leaves         :   29 ( 208 expanded)
%              Depth                    :   23
%              Number of atoms          :  798 (7737 expanded)
%              Number of equality atoms :   52 ( 160 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X14 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','16','17'])).

thf('19',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17
       != ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( ( ( k2_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X8 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ~ ( v1_funct_2 @ sk_A @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','43'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X14 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('48',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('51',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ sk_A )
      = ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17
       != ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ sk_A @ X0 @ X1 )
      | ( v1_funct_2 @ sk_A @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ sk_A @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ sk_A @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('63',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','64','65'])).

thf('67',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('68',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('72',plain,(
    ! [X15: $i] :
      ( zip_tseitin_0 @ X15 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_A @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_A @ k1_xboole_0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['59','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['44','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qKuqW10Fc5
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:59:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 103 iterations in 0.108s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.56  thf(t3_funct_2, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.56       ( ( v1_funct_1 @ A ) & 
% 0.37/0.56         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.37/0.56         ( m1_subset_1 @
% 0.37/0.56           A @ 
% 0.37/0.56           ( k1_zfmisc_1 @
% 0.37/0.56             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.56          ( ( v1_funct_1 @ A ) & 
% 0.37/0.56            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.37/0.56            ( m1_subset_1 @
% 0.37/0.56              A @ 
% 0.37/0.56              ( k1_zfmisc_1 @
% 0.37/0.56                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((~ (v1_funct_1 @ sk_A)
% 0.37/0.56        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.37/0.56        | ~ (m1_subset_1 @ sk_A @ 
% 0.37/0.56             (k1_zfmisc_1 @ 
% 0.37/0.56              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf(d3_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.56  thf('9', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.56  thf(t11_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ C ) =>
% 0.37/0.56       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.37/0.56           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.37/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.37/0.56          | ~ (r1_tarski @ (k2_relat_1 @ X12) @ X14)
% 0.37/0.56          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.37/0.56          | ~ (v1_relat_1 @ X12))),
% 0.37/0.56      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | (m1_subset_1 @ X0 @ 
% 0.37/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.37/0.56          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((m1_subset_1 @ X0 @ 
% 0.37/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['8', '11'])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      ((~ (m1_subset_1 @ sk_A @ 
% 0.37/0.56           (k1_zfmisc_1 @ 
% 0.37/0.56            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((m1_subset_1 @ sk_A @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_A))
% 0.37/0.56         <= (~
% 0.37/0.56             ((m1_subset_1 @ sk_A @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.56  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (((m1_subset_1 @ sk_A @ 
% 0.37/0.56         (k1_zfmisc_1 @ 
% 0.37/0.56          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.37/0.56       ~
% 0.37/0.56       ((m1_subset_1 @ sk_A @ 
% 0.37/0.56         (k1_zfmisc_1 @ 
% 0.37/0.56          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.37/0.56       ~ ((v1_funct_1 @ sk_A))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['4', '16', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.37/0.56      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.37/0.56  thf(d1_funct_2, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_1, axiom,
% 0.37/0.56    (![B:$i,A:$i]:
% 0.37/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i]:
% 0.37/0.56         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((m1_subset_1 @ X0 @ 
% 0.37/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['8', '11'])).
% 0.37/0.56  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.56  thf(zf_stmt_3, axiom,
% 0.37/0.56    (![C:$i,B:$i,A:$i]:
% 0.37/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.56  thf(zf_stmt_5, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.56         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.37/0.56          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.37/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.56          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.37/0.56          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['20', '23'])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((m1_subset_1 @ X0 @ 
% 0.37/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['8', '11'])).
% 0.37/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.56         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.37/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.37/0.56              = (k1_relat_1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.56         (((X17) != (k1_relset_1 @ X17 @ X18 @ X19))
% 0.37/0.56          | (v1_funct_2 @ X19 @ X17 @ X18)
% 0.37/0.56          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.56          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.37/0.56          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['24', '30'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.37/0.56          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.37/0.56      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('36', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.56  thf('37', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '36'])).
% 0.37/0.56  thf('38', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.56  thf(t65_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) =>
% 0.37/0.56       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.37/0.56         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X8 : $i]:
% 0.37/0.56         (((k2_relat_1 @ X8) != (k1_xboole_0))
% 0.37/0.56          | ((k1_relat_1 @ X8) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      ((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.56        | ~ (v1_relat_1 @ sk_A)
% 0.37/0.56        | ((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.56  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      ((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.56        | ((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.56  thf('43', plain, (((k1_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.56  thf('44', plain, (~ (v1_funct_2 @ sk_A @ k1_xboole_0 @ k1_xboole_0)),
% 0.37/0.56      inference('demod', [status(thm)], ['37', '43'])).
% 0.37/0.56  thf('45', plain, (((k1_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.37/0.56          | ~ (r1_tarski @ (k2_relat_1 @ X12) @ X14)
% 0.37/0.56          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.37/0.56          | ~ (v1_relat_1 @ X12))),
% 0.37/0.56      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ sk_A)
% 0.37/0.56          | (m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.37/0.56          | ~ (r1_tarski @ (k2_relat_1 @ sk_A) @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.56  thf('48', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.56  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('50', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.56  thf('51', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.56         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.37/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k1_relset_1 @ X1 @ X0 @ sk_A) = (k1_relat_1 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.56  thf('55', plain, (((k1_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k1_relset_1 @ X1 @ X0 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.56         (((X17) != (k1_relset_1 @ X17 @ X18 @ X19))
% 0.37/0.56          | (v1_funct_2 @ X19 @ X17 @ X18)
% 0.37/0.56          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((X1) != (k1_xboole_0))
% 0.37/0.56          | ~ (zip_tseitin_1 @ sk_A @ X0 @ X1)
% 0.37/0.56          | (v1_funct_2 @ sk_A @ X1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_funct_2 @ sk_A @ k1_xboole_0 @ X0)
% 0.37/0.56          | ~ (zip_tseitin_1 @ sk_A @ X0 @ k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['58'])).
% 0.37/0.56  thf('60', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((m1_subset_1 @ X0 @ 
% 0.37/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['8', '11'])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (((m1_subset_1 @ sk_A @ 
% 0.37/0.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)))
% 0.37/0.56        | ~ (v1_relat_1 @ sk_A))),
% 0.37/0.56      inference('sup+', [status(thm)], ['60', '61'])).
% 0.37/0.56  thf(t113_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.37/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]:
% 0.37/0.56         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['63'])).
% 0.37/0.56  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('66', plain, ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['62', '64', '65'])).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]:
% 0.37/0.56         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['67'])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.56         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.37/0.56          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.37/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.56  thf('70', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.37/0.56          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.37/0.56          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i]:
% 0.37/0.56         ((zip_tseitin_0 @ X15 @ X16) | ((X16) != (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.56  thf('72', plain, (![X15 : $i]: (zip_tseitin_0 @ X15 @ k1_xboole_0)),
% 0.37/0.56      inference('simplify', [status(thm)], ['71'])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.37/0.56          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['70', '72'])).
% 0.37/0.56  thf('74', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_A @ X0 @ k1_xboole_0)),
% 0.37/0.56      inference('sup-', [status(thm)], ['66', '73'])).
% 0.37/0.56  thf('75', plain, (![X0 : $i]: (v1_funct_2 @ sk_A @ k1_xboole_0 @ X0)),
% 0.37/0.56      inference('simplify_reflect+', [status(thm)], ['59', '74'])).
% 0.37/0.56  thf('76', plain, ($false), inference('demod', [status(thm)], ['44', '75'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
