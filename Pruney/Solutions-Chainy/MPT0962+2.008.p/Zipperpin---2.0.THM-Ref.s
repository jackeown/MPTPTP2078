%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fsdSNFTuP7

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:49 EST 2020

% Result     : Theorem 3.60s
% Output     : Refutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 728 expanded)
%              Number of leaves         :   37 ( 229 expanded)
%              Depth                    :   14
%              Number of atoms          :  797 (7865 expanded)
%              Number of equality atoms :   46 ( 178 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X14 @ X12 ) @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X20: $i] :
      ( ( r1_tarski @ X20 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','19','20'])).

thf('22',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

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

thf('23',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

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

thf('25',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf('34',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['26','34'])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','35'])).

thf('37',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','36'])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ sk_B )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','35'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','35'])).

thf('46',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('47',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['40','41','43','44','45','46'])).

thf('48',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['40','41','43','44','45','46'])).

thf('49',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','62'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('75',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['71','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['37','47','48','63','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fsdSNFTuP7
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.60/3.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.60/3.80  % Solved by: fo/fo7.sh
% 3.60/3.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.60/3.80  % done 3401 iterations in 3.362s
% 3.60/3.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.60/3.80  % SZS output start Refutation
% 3.60/3.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.60/3.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.60/3.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.60/3.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.60/3.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.60/3.80  thf(sk_A_type, type, sk_A: $i).
% 3.60/3.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.60/3.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.60/3.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.60/3.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.60/3.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.60/3.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.60/3.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.60/3.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.60/3.80  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.60/3.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.60/3.80  thf(sk_B_type, type, sk_B: $i).
% 3.60/3.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.60/3.80  thf(t4_funct_2, conjecture,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.60/3.80       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.60/3.80         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 3.60/3.80           ( m1_subset_1 @
% 3.60/3.80             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 3.60/3.80  thf(zf_stmt_0, negated_conjecture,
% 3.60/3.80    (~( ![A:$i,B:$i]:
% 3.60/3.80        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.60/3.80          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.60/3.80            ( ( v1_funct_1 @ B ) & 
% 3.60/3.80              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 3.60/3.80              ( m1_subset_1 @
% 3.60/3.80                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 3.60/3.80    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 3.60/3.80  thf('0', plain,
% 3.60/3.80      ((~ (v1_funct_1 @ sk_B)
% 3.60/3.80        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 3.60/3.80        | ~ (m1_subset_1 @ sk_B @ 
% 3.60/3.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 3.60/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.60/3.80  thf('1', plain,
% 3.60/3.80      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 3.60/3.80         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 3.60/3.80      inference('split', [status(esa)], ['0'])).
% 3.60/3.80  thf('2', plain, ((v1_funct_1 @ sk_B)),
% 3.60/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.60/3.80  thf('3', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 3.60/3.80      inference('split', [status(esa)], ['0'])).
% 3.60/3.80  thf('4', plain, (((v1_funct_1 @ sk_B))),
% 3.60/3.80      inference('sup-', [status(thm)], ['2', '3'])).
% 3.60/3.80  thf('5', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 3.60/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.60/3.80  thf(t118_zfmisc_1, axiom,
% 3.60/3.80    (![A:$i,B:$i,C:$i]:
% 3.60/3.80     ( ( r1_tarski @ A @ B ) =>
% 3.60/3.80       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 3.60/3.80         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 3.60/3.80  thf('6', plain,
% 3.60/3.80      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.60/3.80         (~ (r1_tarski @ X12 @ X13)
% 3.60/3.80          | (r1_tarski @ (k2_zfmisc_1 @ X14 @ X12) @ (k2_zfmisc_1 @ X14 @ X13)))),
% 3.60/3.80      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 3.60/3.80  thf('7', plain,
% 3.60/3.80      (![X0 : $i]:
% 3.60/3.80         (r1_tarski @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 3.60/3.80          (k2_zfmisc_1 @ X0 @ sk_A))),
% 3.60/3.80      inference('sup-', [status(thm)], ['5', '6'])).
% 3.60/3.80  thf(t21_relat_1, axiom,
% 3.60/3.80    (![A:$i]:
% 3.60/3.80     ( ( v1_relat_1 @ A ) =>
% 3.60/3.80       ( r1_tarski @
% 3.60/3.80         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 3.60/3.80  thf('8', plain,
% 3.60/3.80      (![X20 : $i]:
% 3.60/3.80         ((r1_tarski @ X20 @ 
% 3.60/3.80           (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20)))
% 3.60/3.80          | ~ (v1_relat_1 @ X20))),
% 3.60/3.80      inference('cnf', [status(esa)], [t21_relat_1])).
% 3.60/3.80  thf(t12_xboole_1, axiom,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.60/3.80  thf('9', plain,
% 3.60/3.80      (![X6 : $i, X7 : $i]:
% 3.60/3.80         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 3.60/3.80      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.60/3.80  thf('10', plain,
% 3.60/3.80      (![X0 : $i]:
% 3.60/3.80         (~ (v1_relat_1 @ X0)
% 3.60/3.80          | ((k2_xboole_0 @ X0 @ 
% 3.60/3.80              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 3.60/3.80              = (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 3.60/3.80      inference('sup-', [status(thm)], ['8', '9'])).
% 3.60/3.80  thf(t11_xboole_1, axiom,
% 3.60/3.80    (![A:$i,B:$i,C:$i]:
% 3.60/3.80     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 3.60/3.80  thf('11', plain,
% 3.60/3.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.60/3.80         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 3.60/3.80      inference('cnf', [status(esa)], [t11_xboole_1])).
% 3.60/3.80  thf('12', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (~ (r1_tarski @ 
% 3.60/3.80             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X1)
% 3.60/3.80          | ~ (v1_relat_1 @ X0)
% 3.60/3.80          | (r1_tarski @ X0 @ X1))),
% 3.60/3.80      inference('sup-', [status(thm)], ['10', '11'])).
% 3.60/3.80  thf('13', plain,
% 3.60/3.80      (((r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))
% 3.60/3.80        | ~ (v1_relat_1 @ sk_B))),
% 3.60/3.80      inference('sup-', [status(thm)], ['7', '12'])).
% 3.60/3.80  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 3.60/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.60/3.80  thf('15', plain,
% 3.60/3.80      ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 3.60/3.80      inference('demod', [status(thm)], ['13', '14'])).
% 3.60/3.80  thf(t3_subset, axiom,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.60/3.80  thf('16', plain,
% 3.60/3.80      (![X15 : $i, X17 : $i]:
% 3.60/3.80         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 3.60/3.80      inference('cnf', [status(esa)], [t3_subset])).
% 3.60/3.80  thf('17', plain,
% 3.60/3.80      ((m1_subset_1 @ sk_B @ 
% 3.60/3.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 3.60/3.80      inference('sup-', [status(thm)], ['15', '16'])).
% 3.60/3.80  thf('18', plain,
% 3.60/3.80      ((~ (m1_subset_1 @ sk_B @ 
% 3.60/3.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 3.60/3.80         <= (~
% 3.60/3.80             ((m1_subset_1 @ sk_B @ 
% 3.60/3.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 3.60/3.80      inference('split', [status(esa)], ['0'])).
% 3.60/3.80  thf('19', plain,
% 3.60/3.80      (((m1_subset_1 @ sk_B @ 
% 3.60/3.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 3.60/3.80      inference('sup-', [status(thm)], ['17', '18'])).
% 3.60/3.80  thf('20', plain,
% 3.60/3.80      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 3.60/3.80       ~
% 3.60/3.80       ((m1_subset_1 @ sk_B @ 
% 3.60/3.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 3.60/3.80       ~ ((v1_funct_1 @ sk_B))),
% 3.60/3.80      inference('split', [status(esa)], ['0'])).
% 3.60/3.80  thf('21', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 3.60/3.80      inference('sat_resolution*', [status(thm)], ['4', '19', '20'])).
% 3.60/3.80  thf('22', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 3.60/3.80      inference('simpl_trail', [status(thm)], ['1', '21'])).
% 3.60/3.80  thf(d1_funct_2, axiom,
% 3.60/3.80    (![A:$i,B:$i,C:$i]:
% 3.60/3.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.60/3.80       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.60/3.80           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.60/3.80             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.60/3.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.60/3.80           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.60/3.80             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.60/3.80  thf(zf_stmt_1, axiom,
% 3.60/3.80    (![B:$i,A:$i]:
% 3.60/3.80     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.60/3.80       ( zip_tseitin_0 @ B @ A ) ))).
% 3.60/3.80  thf('23', plain,
% 3.60/3.80      (![X30 : $i, X31 : $i]:
% 3.60/3.80         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 3.60/3.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.60/3.80  thf('24', plain,
% 3.60/3.80      ((m1_subset_1 @ sk_B @ 
% 3.60/3.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 3.60/3.80      inference('sup-', [status(thm)], ['15', '16'])).
% 3.60/3.80  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.60/3.80  thf(zf_stmt_3, axiom,
% 3.60/3.80    (![C:$i,B:$i,A:$i]:
% 3.60/3.80     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.60/3.80       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.60/3.80  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.60/3.80  thf(zf_stmt_5, axiom,
% 3.60/3.80    (![A:$i,B:$i,C:$i]:
% 3.60/3.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.60/3.80       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.60/3.80         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.60/3.80           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.60/3.80             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.60/3.80  thf('25', plain,
% 3.60/3.80      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.60/3.80         (~ (zip_tseitin_0 @ X35 @ X36)
% 3.60/3.80          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 3.60/3.80          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 3.60/3.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.60/3.80  thf('26', plain,
% 3.60/3.80      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 3.60/3.80        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 3.60/3.80      inference('sup-', [status(thm)], ['24', '25'])).
% 3.60/3.80  thf('27', plain,
% 3.60/3.80      ((m1_subset_1 @ sk_B @ 
% 3.60/3.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 3.60/3.80      inference('sup-', [status(thm)], ['15', '16'])).
% 3.60/3.80  thf(redefinition_k1_relset_1, axiom,
% 3.60/3.80    (![A:$i,B:$i,C:$i]:
% 3.60/3.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.60/3.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.60/3.80  thf('28', plain,
% 3.60/3.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.60/3.80         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 3.60/3.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.60/3.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.60/3.80  thf('29', plain,
% 3.60/3.80      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 3.60/3.80      inference('sup-', [status(thm)], ['27', '28'])).
% 3.60/3.80  thf('30', plain,
% 3.60/3.80      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.60/3.80         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 3.60/3.80          | (v1_funct_2 @ X34 @ X32 @ X33)
% 3.60/3.80          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 3.60/3.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.60/3.80  thf('31', plain,
% 3.60/3.80      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 3.60/3.80        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 3.60/3.80        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 3.60/3.80      inference('sup-', [status(thm)], ['29', '30'])).
% 3.60/3.80  thf('32', plain,
% 3.60/3.80      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 3.60/3.80        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 3.60/3.80      inference('simplify', [status(thm)], ['31'])).
% 3.60/3.80  thf('33', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 3.60/3.80      inference('simpl_trail', [status(thm)], ['1', '21'])).
% 3.60/3.80  thf('34', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 3.60/3.80      inference('clc', [status(thm)], ['32', '33'])).
% 3.60/3.80  thf('35', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 3.60/3.80      inference('clc', [status(thm)], ['26', '34'])).
% 3.60/3.80  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['23', '35'])).
% 3.60/3.80  thf('37', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ k1_xboole_0)),
% 3.60/3.80      inference('demod', [status(thm)], ['22', '36'])).
% 3.60/3.80  thf('38', plain,
% 3.60/3.80      ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 3.60/3.80      inference('demod', [status(thm)], ['13', '14'])).
% 3.60/3.80  thf(d10_xboole_0, axiom,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.60/3.80  thf('39', plain,
% 3.60/3.80      (![X0 : $i, X2 : $i]:
% 3.60/3.80         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.60/3.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.60/3.80  thf('40', plain,
% 3.60/3.80      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A) @ sk_B)
% 3.60/3.80        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A) = (sk_B)))),
% 3.60/3.80      inference('sup-', [status(thm)], ['38', '39'])).
% 3.60/3.80  thf('41', plain, (((sk_A) = (k1_xboole_0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['23', '35'])).
% 3.60/3.80  thf(t113_zfmisc_1, axiom,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.60/3.80       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.60/3.80  thf('42', plain,
% 3.60/3.80      (![X10 : $i, X11 : $i]:
% 3.60/3.80         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 3.60/3.80          | ((X11) != (k1_xboole_0)))),
% 3.60/3.80      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.60/3.80  thf('43', plain,
% 3.60/3.80      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 3.60/3.80      inference('simplify', [status(thm)], ['42'])).
% 3.60/3.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.60/3.80  thf('44', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 3.60/3.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.60/3.80  thf('45', plain, (((sk_A) = (k1_xboole_0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['23', '35'])).
% 3.60/3.80  thf('46', plain,
% 3.60/3.80      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 3.60/3.80      inference('simplify', [status(thm)], ['42'])).
% 3.60/3.80  thf('47', plain, (((k1_xboole_0) = (sk_B))),
% 3.60/3.80      inference('demod', [status(thm)], ['40', '41', '43', '44', '45', '46'])).
% 3.60/3.80  thf('48', plain, (((k1_xboole_0) = (sk_B))),
% 3.60/3.80      inference('demod', [status(thm)], ['40', '41', '43', '44', '45', '46'])).
% 3.60/3.80  thf('49', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 3.60/3.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.60/3.80  thf('50', plain,
% 3.60/3.80      (![X15 : $i, X17 : $i]:
% 3.60/3.80         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 3.60/3.80      inference('cnf', [status(esa)], [t3_subset])).
% 3.60/3.80  thf('51', plain,
% 3.60/3.80      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['49', '50'])).
% 3.60/3.80  thf(cc2_relset_1, axiom,
% 3.60/3.80    (![A:$i,B:$i,C:$i]:
% 3.60/3.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.60/3.80       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.60/3.80  thf('52', plain,
% 3.60/3.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.60/3.80         ((v4_relat_1 @ X24 @ X25)
% 3.60/3.80          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.60/3.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.60/3.80  thf('53', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 3.60/3.80      inference('sup-', [status(thm)], ['51', '52'])).
% 3.60/3.80  thf(d18_relat_1, axiom,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( v1_relat_1 @ B ) =>
% 3.60/3.80       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.60/3.80  thf('54', plain,
% 3.60/3.80      (![X18 : $i, X19 : $i]:
% 3.60/3.80         (~ (v4_relat_1 @ X18 @ X19)
% 3.60/3.80          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 3.60/3.80          | ~ (v1_relat_1 @ X18))),
% 3.60/3.80      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.60/3.80  thf('55', plain,
% 3.60/3.80      (![X0 : $i]:
% 3.60/3.80         (~ (v1_relat_1 @ k1_xboole_0)
% 3.60/3.80          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['53', '54'])).
% 3.60/3.80  thf('56', plain,
% 3.60/3.80      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['49', '50'])).
% 3.60/3.80  thf(cc1_relset_1, axiom,
% 3.60/3.80    (![A:$i,B:$i,C:$i]:
% 3.60/3.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.60/3.80       ( v1_relat_1 @ C ) ))).
% 3.60/3.80  thf('57', plain,
% 3.60/3.80      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.60/3.80         ((v1_relat_1 @ X21)
% 3.60/3.80          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.60/3.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.60/3.80  thf('58', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.60/3.80      inference('sup-', [status(thm)], ['56', '57'])).
% 3.60/3.80  thf('59', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 3.60/3.80      inference('demod', [status(thm)], ['55', '58'])).
% 3.60/3.80  thf('60', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 3.60/3.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.60/3.80  thf('61', plain,
% 3.60/3.80      (![X0 : $i, X2 : $i]:
% 3.60/3.80         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.60/3.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.60/3.80  thf('62', plain,
% 3.60/3.80      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.60/3.80      inference('sup-', [status(thm)], ['60', '61'])).
% 3.60/3.80  thf('63', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['59', '62'])).
% 3.60/3.80  thf('64', plain,
% 3.60/3.80      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['49', '50'])).
% 3.60/3.80  thf('65', plain,
% 3.60/3.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.60/3.80         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 3.60/3.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.60/3.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.60/3.80  thf('66', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['64', '65'])).
% 3.60/3.80  thf('67', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['59', '62'])).
% 3.60/3.80  thf('68', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.60/3.80      inference('demod', [status(thm)], ['66', '67'])).
% 3.60/3.80  thf('69', plain,
% 3.60/3.80      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.60/3.80         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 3.60/3.80          | (v1_funct_2 @ X34 @ X32 @ X33)
% 3.60/3.80          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 3.60/3.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.60/3.80  thf('70', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (((X1) != (k1_xboole_0))
% 3.60/3.80          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 3.60/3.80          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['68', '69'])).
% 3.60/3.80  thf('71', plain,
% 3.60/3.80      (![X0 : $i]:
% 3.60/3.80         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.60/3.80          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 3.60/3.80      inference('simplify', [status(thm)], ['70'])).
% 3.60/3.80  thf('72', plain,
% 3.60/3.80      (![X30 : $i, X31 : $i]:
% 3.60/3.80         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 3.60/3.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.60/3.80  thf('73', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 3.60/3.80      inference('simplify', [status(thm)], ['72'])).
% 3.60/3.80  thf('74', plain,
% 3.60/3.80      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.60/3.80      inference('sup-', [status(thm)], ['49', '50'])).
% 3.60/3.80  thf('75', plain,
% 3.60/3.80      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.60/3.80         (~ (zip_tseitin_0 @ X35 @ X36)
% 3.60/3.80          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 3.60/3.80          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 3.60/3.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.60/3.80  thf('76', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.60/3.80      inference('sup-', [status(thm)], ['74', '75'])).
% 3.60/3.80  thf('77', plain,
% 3.60/3.80      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.60/3.80      inference('sup-', [status(thm)], ['73', '76'])).
% 3.60/3.80  thf('78', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.60/3.80      inference('demod', [status(thm)], ['71', '77'])).
% 3.60/3.80  thf('79', plain, ($false),
% 3.60/3.80      inference('demod', [status(thm)], ['37', '47', '48', '63', '78'])).
% 3.60/3.80  
% 3.60/3.80  % SZS output end Refutation
% 3.60/3.80  
% 3.60/3.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
