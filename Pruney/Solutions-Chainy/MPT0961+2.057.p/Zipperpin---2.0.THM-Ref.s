%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.75aSsllYUK

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:46 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 492 expanded)
%              Number of leaves         :   32 ( 153 expanded)
%              Depth                    :   16
%              Number of atoms          :  870 (4927 expanded)
%              Number of equality atoms :   71 ( 190 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X23 )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
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

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( ( ( k2_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('45',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,(
    ! [X8: $i] :
      ( ( ( k2_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('52',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('54',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('58',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['53','63'])).

thf('65',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['50','51'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('69',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('71',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('72',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('74',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('76',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('77',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','72','74','77'])).

thf('79',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('80',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('83',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','85'])).

thf('87',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['37','43','44','52','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.75aSsllYUK
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:52:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.57/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.73  % Solved by: fo/fo7.sh
% 0.57/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.73  % done 291 iterations in 0.273s
% 0.57/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.73  % SZS output start Refutation
% 0.57/0.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.57/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.57/0.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.57/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.57/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.57/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.57/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.57/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.57/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.57/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.57/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.57/0.73  thf(t3_funct_2, conjecture,
% 0.57/0.73    (![A:$i]:
% 0.57/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.57/0.73       ( ( v1_funct_1 @ A ) & 
% 0.57/0.73         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.57/0.73         ( m1_subset_1 @
% 0.57/0.73           A @ 
% 0.57/0.73           ( k1_zfmisc_1 @
% 0.57/0.73             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.57/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.73    (~( ![A:$i]:
% 0.57/0.73        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.57/0.73          ( ( v1_funct_1 @ A ) & 
% 0.57/0.73            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.57/0.73            ( m1_subset_1 @
% 0.57/0.73              A @ 
% 0.57/0.73              ( k1_zfmisc_1 @
% 0.57/0.73                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.57/0.73    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.57/0.73  thf('0', plain,
% 0.57/0.73      ((~ (v1_funct_1 @ sk_A)
% 0.57/0.73        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.57/0.73        | ~ (m1_subset_1 @ sk_A @ 
% 0.57/0.73             (k1_zfmisc_1 @ 
% 0.57/0.73              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('1', plain,
% 0.57/0.73      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.57/0.73         <= (~
% 0.57/0.73             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.57/0.73      inference('split', [status(esa)], ['0'])).
% 0.57/0.73  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.57/0.73      inference('split', [status(esa)], ['0'])).
% 0.57/0.73  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.57/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.57/0.73  thf(d3_tarski, axiom,
% 0.57/0.73    (![A:$i,B:$i]:
% 0.57/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.57/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.57/0.73  thf('5', plain,
% 0.57/0.73      (![X1 : $i, X3 : $i]:
% 0.57/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.57/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.73  thf('6', plain,
% 0.57/0.73      (![X1 : $i, X3 : $i]:
% 0.57/0.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.57/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.73  thf('7', plain,
% 0.57/0.73      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.57/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.57/0.73  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.57/0.73      inference('simplify', [status(thm)], ['7'])).
% 0.57/0.73  thf('9', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.57/0.73      inference('simplify', [status(thm)], ['7'])).
% 0.57/0.73  thf(t11_relset_1, axiom,
% 0.57/0.73    (![A:$i,B:$i,C:$i]:
% 0.57/0.73     ( ( v1_relat_1 @ C ) =>
% 0.57/0.73       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.57/0.73           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.57/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.57/0.73  thf('10', plain,
% 0.57/0.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.57/0.73         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.57/0.73          | ~ (r1_tarski @ (k2_relat_1 @ X21) @ X23)
% 0.57/0.73          | (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.57/0.73          | ~ (v1_relat_1 @ X21))),
% 0.57/0.73      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.57/0.73  thf('11', plain,
% 0.57/0.73      (![X0 : $i, X1 : $i]:
% 0.57/0.73         (~ (v1_relat_1 @ X0)
% 0.57/0.73          | (m1_subset_1 @ X0 @ 
% 0.57/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.57/0.73          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.57/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.57/0.73  thf('12', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         ((m1_subset_1 @ X0 @ 
% 0.57/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.57/0.73          | ~ (v1_relat_1 @ X0))),
% 0.57/0.73      inference('sup-', [status(thm)], ['8', '11'])).
% 0.57/0.73  thf('13', plain,
% 0.57/0.73      ((~ (m1_subset_1 @ sk_A @ 
% 0.57/0.73           (k1_zfmisc_1 @ 
% 0.57/0.73            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.57/0.73         <= (~
% 0.57/0.73             ((m1_subset_1 @ sk_A @ 
% 0.57/0.73               (k1_zfmisc_1 @ 
% 0.57/0.73                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.57/0.73      inference('split', [status(esa)], ['0'])).
% 0.57/0.73  thf('14', plain,
% 0.57/0.73      ((~ (v1_relat_1 @ sk_A))
% 0.57/0.73         <= (~
% 0.57/0.73             ((m1_subset_1 @ sk_A @ 
% 0.57/0.73               (k1_zfmisc_1 @ 
% 0.57/0.73                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.57/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.57/0.73  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('16', plain,
% 0.57/0.73      (((m1_subset_1 @ sk_A @ 
% 0.57/0.73         (k1_zfmisc_1 @ 
% 0.57/0.73          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.57/0.73      inference('demod', [status(thm)], ['14', '15'])).
% 0.57/0.73  thf('17', plain,
% 0.57/0.73      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.57/0.73       ~
% 0.57/0.73       ((m1_subset_1 @ sk_A @ 
% 0.57/0.73         (k1_zfmisc_1 @ 
% 0.57/0.73          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.57/0.73       ~ ((v1_funct_1 @ sk_A))),
% 0.57/0.73      inference('split', [status(esa)], ['0'])).
% 0.57/0.73  thf('18', plain,
% 0.57/0.73      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.57/0.73      inference('sat_resolution*', [status(thm)], ['4', '16', '17'])).
% 0.57/0.73  thf('19', plain,
% 0.57/0.73      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.57/0.73      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.57/0.73  thf(d1_funct_2, axiom,
% 0.57/0.73    (![A:$i,B:$i,C:$i]:
% 0.57/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.57/0.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.57/0.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.57/0.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.57/0.73  thf(zf_stmt_1, axiom,
% 0.57/0.73    (![B:$i,A:$i]:
% 0.57/0.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.73       ( zip_tseitin_0 @ B @ A ) ))).
% 0.57/0.73  thf('20', plain,
% 0.57/0.73      (![X24 : $i, X25 : $i]:
% 0.57/0.73         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.57/0.73  thf('21', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         ((m1_subset_1 @ X0 @ 
% 0.57/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.57/0.73          | ~ (v1_relat_1 @ X0))),
% 0.57/0.73      inference('sup-', [status(thm)], ['8', '11'])).
% 0.57/0.73  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.57/0.73  thf(zf_stmt_3, axiom,
% 0.57/0.73    (![C:$i,B:$i,A:$i]:
% 0.57/0.73     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.57/0.73       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.57/0.73  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.57/0.73  thf(zf_stmt_5, axiom,
% 0.57/0.73    (![A:$i,B:$i,C:$i]:
% 0.57/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.73       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.57/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.57/0.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.57/0.73  thf('22', plain,
% 0.57/0.73      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.57/0.73         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.57/0.73          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.57/0.73          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.57/0.73  thf('23', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         (~ (v1_relat_1 @ X0)
% 0.57/0.73          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.57/0.73          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.57/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.57/0.73  thf('24', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.57/0.73          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.57/0.73          | ~ (v1_relat_1 @ X0))),
% 0.57/0.73      inference('sup-', [status(thm)], ['20', '23'])).
% 0.57/0.73  thf('25', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         ((m1_subset_1 @ X0 @ 
% 0.57/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.57/0.73          | ~ (v1_relat_1 @ X0))),
% 0.57/0.73      inference('sup-', [status(thm)], ['8', '11'])).
% 0.57/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.57/0.73    (![A:$i,B:$i,C:$i]:
% 0.57/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.57/0.73  thf('26', plain,
% 0.57/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.57/0.73         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.57/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.57/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.57/0.73  thf('27', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         (~ (v1_relat_1 @ X0)
% 0.57/0.73          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.57/0.73              = (k1_relat_1 @ X0)))),
% 0.57/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.57/0.73  thf('28', plain,
% 0.57/0.73      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.57/0.73         (((X26) != (k1_relset_1 @ X26 @ X27 @ X28))
% 0.57/0.73          | (v1_funct_2 @ X28 @ X26 @ X27)
% 0.57/0.73          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.57/0.73  thf('29', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.57/0.73          | ~ (v1_relat_1 @ X0)
% 0.57/0.73          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.57/0.73          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.57/0.73      inference('sup-', [status(thm)], ['27', '28'])).
% 0.57/0.73  thf('30', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.57/0.73          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.57/0.73          | ~ (v1_relat_1 @ X0))),
% 0.57/0.73      inference('simplify', [status(thm)], ['29'])).
% 0.57/0.73  thf('31', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         (~ (v1_relat_1 @ X0)
% 0.57/0.73          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.57/0.73          | ~ (v1_relat_1 @ X0)
% 0.57/0.73          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.57/0.73      inference('sup-', [status(thm)], ['24', '30'])).
% 0.57/0.73  thf('32', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.57/0.73          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.57/0.73          | ~ (v1_relat_1 @ X0))),
% 0.57/0.73      inference('simplify', [status(thm)], ['31'])).
% 0.57/0.73  thf('33', plain,
% 0.57/0.73      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.57/0.73      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.57/0.73  thf('34', plain,
% 0.57/0.73      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.57/0.73      inference('sup-', [status(thm)], ['32', '33'])).
% 0.57/0.73  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('36', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.57/0.73      inference('demod', [status(thm)], ['34', '35'])).
% 0.57/0.73  thf('37', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.57/0.73      inference('demod', [status(thm)], ['19', '36'])).
% 0.57/0.73  thf('38', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.57/0.73      inference('demod', [status(thm)], ['34', '35'])).
% 0.57/0.73  thf(t64_relat_1, axiom,
% 0.57/0.73    (![A:$i]:
% 0.57/0.73     ( ( v1_relat_1 @ A ) =>
% 0.57/0.73       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.57/0.73           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.73         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.57/0.73  thf('39', plain,
% 0.57/0.73      (![X8 : $i]:
% 0.57/0.73         (((k2_relat_1 @ X8) != (k1_xboole_0))
% 0.57/0.73          | ((X8) = (k1_xboole_0))
% 0.57/0.73          | ~ (v1_relat_1 @ X8))),
% 0.57/0.73      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.57/0.73  thf('40', plain,
% 0.57/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.57/0.73        | ~ (v1_relat_1 @ sk_A)
% 0.57/0.73        | ((sk_A) = (k1_xboole_0)))),
% 0.57/0.73      inference('sup-', [status(thm)], ['38', '39'])).
% 0.57/0.73  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('42', plain,
% 0.57/0.73      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.57/0.73      inference('demod', [status(thm)], ['40', '41'])).
% 0.57/0.73  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.57/0.73      inference('simplify', [status(thm)], ['42'])).
% 0.57/0.73  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.57/0.73      inference('simplify', [status(thm)], ['42'])).
% 0.57/0.73  thf(t71_relat_1, axiom,
% 0.57/0.73    (![A:$i]:
% 0.57/0.73     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.57/0.73       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.57/0.73  thf('45', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.57/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.57/0.73  thf('46', plain,
% 0.57/0.73      (![X8 : $i]:
% 0.57/0.73         (((k2_relat_1 @ X8) != (k1_xboole_0))
% 0.57/0.73          | ((X8) = (k1_xboole_0))
% 0.57/0.73          | ~ (v1_relat_1 @ X8))),
% 0.57/0.73      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.57/0.73  thf('47', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         (((X0) != (k1_xboole_0))
% 0.57/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.57/0.73          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.57/0.73      inference('sup-', [status(thm)], ['45', '46'])).
% 0.57/0.73  thf(fc4_funct_1, axiom,
% 0.57/0.73    (![A:$i]:
% 0.57/0.73     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.57/0.73       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.57/0.73  thf('48', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.57/0.73      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.57/0.73  thf('49', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         (((X0) != (k1_xboole_0)) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.57/0.73      inference('demod', [status(thm)], ['47', '48'])).
% 0.57/0.73  thf('50', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.73      inference('simplify', [status(thm)], ['49'])).
% 0.57/0.73  thf('51', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.57/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.57/0.73  thf('52', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.73      inference('sup+', [status(thm)], ['50', '51'])).
% 0.57/0.73  thf('53', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.73      inference('simplify', [status(thm)], ['49'])).
% 0.57/0.73  thf('54', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.57/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.57/0.73  thf('55', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         ((m1_subset_1 @ X0 @ 
% 0.57/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.57/0.73          | ~ (v1_relat_1 @ X0))),
% 0.57/0.73      inference('sup-', [status(thm)], ['8', '11'])).
% 0.57/0.73  thf('56', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         ((m1_subset_1 @ (k6_relat_1 @ X0) @ 
% 0.57/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))
% 0.57/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.57/0.73      inference('sup+', [status(thm)], ['54', '55'])).
% 0.57/0.73  thf('57', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.57/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.57/0.73  thf('58', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.57/0.73      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.57/0.73  thf('59', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         (m1_subset_1 @ (k6_relat_1 @ X0) @ 
% 0.57/0.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))),
% 0.57/0.73      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.57/0.73  thf('60', plain,
% 0.57/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.57/0.73         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.57/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.57/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.57/0.73  thf('61', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         ((k1_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0))
% 0.57/0.73           = (k1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.57/0.73      inference('sup-', [status(thm)], ['59', '60'])).
% 0.57/0.73  thf('62', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.57/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.57/0.73  thf('63', plain,
% 0.57/0.73      (![X0 : $i]: ((k1_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0)) = (X0))),
% 0.57/0.73      inference('demod', [status(thm)], ['61', '62'])).
% 0.57/0.73  thf('64', plain,
% 0.57/0.73      (((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.73      inference('sup+', [status(thm)], ['53', '63'])).
% 0.57/0.73  thf('65', plain,
% 0.57/0.73      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.57/0.73         (((X26) != (k1_relset_1 @ X26 @ X27 @ X28))
% 0.57/0.73          | (v1_funct_2 @ X28 @ X26 @ X27)
% 0.57/0.73          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.57/0.73  thf('66', plain,
% 0.57/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.57/0.73        | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.73        | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.57/0.73      inference('sup-', [status(thm)], ['64', '65'])).
% 0.57/0.73  thf('67', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.73      inference('sup+', [status(thm)], ['50', '51'])).
% 0.57/0.73  thf('68', plain,
% 0.57/0.73      (![X0 : $i]:
% 0.57/0.73         ((m1_subset_1 @ X0 @ 
% 0.57/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.57/0.73          | ~ (v1_relat_1 @ X0))),
% 0.57/0.73      inference('sup-', [status(thm)], ['8', '11'])).
% 0.57/0.73  thf('69', plain,
% 0.57/0.73      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.57/0.73         (k1_zfmisc_1 @ 
% 0.57/0.73          (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))))
% 0.57/0.73        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.57/0.73      inference('sup+', [status(thm)], ['67', '68'])).
% 0.57/0.73  thf('70', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.73      inference('simplify', [status(thm)], ['49'])).
% 0.57/0.73  thf('71', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.57/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.57/0.73  thf('72', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.73      inference('sup+', [status(thm)], ['70', '71'])).
% 0.57/0.73  thf(t113_zfmisc_1, axiom,
% 0.57/0.73    (![A:$i,B:$i]:
% 0.57/0.73     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.57/0.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.57/0.73  thf('73', plain,
% 0.57/0.73      (![X5 : $i, X6 : $i]:
% 0.57/0.73         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.57/0.73      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.57/0.73  thf('74', plain,
% 0.57/0.73      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.57/0.73      inference('simplify', [status(thm)], ['73'])).
% 0.57/0.73  thf('75', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.73      inference('simplify', [status(thm)], ['49'])).
% 0.57/0.73  thf('76', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.57/0.73      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.57/0.73  thf('77', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.57/0.73      inference('sup+', [status(thm)], ['75', '76'])).
% 0.57/0.73  thf('78', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.57/0.73      inference('demod', [status(thm)], ['69', '72', '74', '77'])).
% 0.57/0.73  thf('79', plain,
% 0.57/0.73      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.57/0.73      inference('simplify', [status(thm)], ['73'])).
% 0.57/0.73  thf('80', plain,
% 0.57/0.73      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.57/0.73         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.57/0.73          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.57/0.73          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.57/0.73  thf('81', plain,
% 0.57/0.73      (![X0 : $i, X1 : $i]:
% 0.57/0.73         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.57/0.73          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.57/0.73          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.57/0.73      inference('sup-', [status(thm)], ['79', '80'])).
% 0.57/0.73  thf('82', plain,
% 0.57/0.73      (![X24 : $i, X25 : $i]:
% 0.57/0.73         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.57/0.73  thf('83', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 0.57/0.73      inference('simplify', [status(thm)], ['82'])).
% 0.57/0.73  thf('84', plain,
% 0.57/0.73      (![X0 : $i, X1 : $i]:
% 0.57/0.73         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.57/0.73          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.57/0.73      inference('demod', [status(thm)], ['81', '83'])).
% 0.57/0.73  thf('85', plain,
% 0.57/0.73      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.57/0.73      inference('sup-', [status(thm)], ['78', '84'])).
% 0.57/0.73  thf('86', plain,
% 0.57/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.57/0.73        | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.57/0.73      inference('demod', [status(thm)], ['66', '85'])).
% 0.57/0.73  thf('87', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.57/0.73      inference('simplify', [status(thm)], ['86'])).
% 0.57/0.73  thf('88', plain, ($false),
% 0.57/0.73      inference('demod', [status(thm)], ['37', '43', '44', '52', '87'])).
% 0.57/0.73  
% 0.57/0.73  % SZS output end Refutation
% 0.57/0.73  
% 0.57/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
