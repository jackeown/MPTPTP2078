%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CaE51Dzi1R

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:41 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  157 (3912 expanded)
%              Number of leaves         :   29 (1039 expanded)
%              Depth                    :   24
%              Number of atoms          : 1210 (42811 expanded)
%              Number of equality atoms :   69 (1356 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X18 )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','14','15'])).

thf('17',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

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

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

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

thf('26',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21
       != ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['39','40'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('45',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('46',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','43','44','45'])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','43','44','45'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('57',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','58'])).

thf('60',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ( X26 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,(
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('63',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','63'])).

thf('65',plain,
    ( ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0 ) )
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('67',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('72',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['64'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('75',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('76',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['73','78'])).

thf('80',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 )
        | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['64'])).

thf('96',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0 ) ) ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['65','96'])).

thf('98',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','58'])).

thf('99',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','99'])).

thf('101',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','57'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('103',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('105',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('106',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('108',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21
       != ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('117',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('118',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('122',plain,(
    ! [X19: $i] :
      ( zip_tseitin_0 @ X19 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['120','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','123'])).

thf('125',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect+',[status(thm)],['115','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['100','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CaE51Dzi1R
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:30:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 285 iterations in 0.266s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.70  thf(t3_funct_2, conjecture,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.70       ( ( v1_funct_1 @ A ) & 
% 0.47/0.70         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.47/0.70         ( m1_subset_1 @
% 0.47/0.70           A @ 
% 0.47/0.70           ( k1_zfmisc_1 @
% 0.47/0.70             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i]:
% 0.47/0.70        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.70          ( ( v1_funct_1 @ A ) & 
% 0.47/0.70            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.47/0.70            ( m1_subset_1 @
% 0.47/0.70              A @ 
% 0.47/0.70              ( k1_zfmisc_1 @
% 0.47/0.70                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.47/0.70  thf('0', plain,
% 0.47/0.70      ((~ (v1_funct_1 @ sk_A)
% 0.47/0.70        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.47/0.70        | ~ (m1_subset_1 @ sk_A @ 
% 0.47/0.70             (k1_zfmisc_1 @ 
% 0.47/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('1', plain,
% 0.47/0.70      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.47/0.70         <= (~
% 0.47/0.70             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.47/0.70      inference('split', [status(esa)], ['0'])).
% 0.47/0.70  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.47/0.70      inference('split', [status(esa)], ['0'])).
% 0.47/0.70  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.70  thf(d10_xboole_0, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.70  thf('5', plain,
% 0.47/0.70      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.47/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.70  thf('6', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.47/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.70  thf('7', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.47/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.70  thf(t11_relset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ C ) =>
% 0.47/0.70       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.47/0.70           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.47/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.47/0.70  thf('8', plain,
% 0.47/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.70         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.47/0.70          | ~ (r1_tarski @ (k2_relat_1 @ X16) @ X18)
% 0.47/0.70          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.47/0.70          | ~ (v1_relat_1 @ X16))),
% 0.47/0.70      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.47/0.70  thf('9', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (m1_subset_1 @ X0 @ 
% 0.47/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.47/0.70          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.70  thf('10', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X0 @ 
% 0.47/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['6', '9'])).
% 0.47/0.70  thf('11', plain,
% 0.47/0.70      ((~ (m1_subset_1 @ sk_A @ 
% 0.47/0.70           (k1_zfmisc_1 @ 
% 0.47/0.70            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.47/0.70         <= (~
% 0.47/0.70             ((m1_subset_1 @ sk_A @ 
% 0.47/0.70               (k1_zfmisc_1 @ 
% 0.47/0.70                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.47/0.70      inference('split', [status(esa)], ['0'])).
% 0.47/0.70  thf('12', plain,
% 0.47/0.70      ((~ (v1_relat_1 @ sk_A))
% 0.47/0.70         <= (~
% 0.47/0.70             ((m1_subset_1 @ sk_A @ 
% 0.47/0.70               (k1_zfmisc_1 @ 
% 0.47/0.70                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.70  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('14', plain,
% 0.47/0.70      (((m1_subset_1 @ sk_A @ 
% 0.47/0.70         (k1_zfmisc_1 @ 
% 0.47/0.70          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.47/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.70  thf('15', plain,
% 0.47/0.70      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.47/0.70       ~
% 0.47/0.70       ((m1_subset_1 @ sk_A @ 
% 0.47/0.70         (k1_zfmisc_1 @ 
% 0.47/0.70          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.47/0.70       ~ ((v1_funct_1 @ sk_A))),
% 0.47/0.70      inference('split', [status(esa)], ['0'])).
% 0.47/0.70  thf('16', plain,
% 0.47/0.70      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.47/0.70      inference('sat_resolution*', [status(thm)], ['4', '14', '15'])).
% 0.47/0.70  thf('17', plain,
% 0.47/0.70      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.47/0.70  thf(d1_funct_2, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_1, axiom,
% 0.47/0.70    (![B:$i,A:$i]:
% 0.47/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.70  thf('18', plain,
% 0.47/0.70      (![X19 : $i, X20 : $i]:
% 0.47/0.70         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.70  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.70  thf('20', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.47/0.70      inference('sup+', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('21', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X0 @ 
% 0.47/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['6', '9'])).
% 0.47/0.70  thf(cc4_relset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( v1_xboole_0 @ A ) =>
% 0.47/0.70       ( ![C:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.47/0.70           ( v1_xboole_0 @ C ) ) ) ))).
% 0.47/0.70  thf('22', plain,
% 0.47/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.70         (~ (v1_xboole_0 @ X7)
% 0.47/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 0.47/0.70          | (v1_xboole_0 @ X8))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.47/0.70  thf('23', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (v1_xboole_0 @ X0)
% 0.47/0.70          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.70  thf('24', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 0.47/0.70          | (v1_xboole_0 @ X0)
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['20', '23'])).
% 0.47/0.70  thf('25', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X0 @ 
% 0.47/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['6', '9'])).
% 0.47/0.70  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.70  thf(zf_stmt_3, axiom,
% 0.47/0.70    (![C:$i,B:$i,A:$i]:
% 0.47/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.70  thf(zf_stmt_5, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.70  thf('26', plain,
% 0.47/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.70         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.47/0.70          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.47/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.70  thf('27', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.70  thf('28', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (v1_xboole_0 @ X0)
% 0.47/0.70          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['24', '27'])).
% 0.47/0.70  thf('29', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70          | (v1_xboole_0 @ X0)
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['28'])).
% 0.47/0.70  thf('30', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X0 @ 
% 0.47/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['6', '9'])).
% 0.47/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.70  thf('31', plain,
% 0.47/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.70         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.47/0.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.70  thf('32', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.47/0.70              = (k1_relat_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.70  thf('33', plain,
% 0.47/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.70         (((X21) != (k1_relset_1 @ X21 @ X22 @ X23))
% 0.47/0.70          | (v1_funct_2 @ X23 @ X21 @ X22)
% 0.47/0.70          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.70  thf('34', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.47/0.70          | ~ (v1_relat_1 @ X0)
% 0.47/0.70          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.70  thf('35', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.70          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['34'])).
% 0.47/0.70  thf('36', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (v1_xboole_0 @ X0)
% 0.47/0.70          | ~ (v1_relat_1 @ X0)
% 0.47/0.70          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['29', '35'])).
% 0.47/0.70  thf('37', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.70          | (v1_xboole_0 @ X0)
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['36'])).
% 0.47/0.70  thf('38', plain,
% 0.47/0.70      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.47/0.70  thf('39', plain, ((~ (v1_relat_1 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.70  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('41', plain, ((v1_xboole_0 @ sk_A)),
% 0.47/0.70      inference('demod', [status(thm)], ['39', '40'])).
% 0.47/0.70  thf(l13_xboole_0, axiom,
% 0.47/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.70  thf('42', plain,
% 0.47/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.70  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.70  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.70  thf('45', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.70  thf('46', plain,
% 0.47/0.70      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.47/0.70          (k2_relat_1 @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['17', '43', '44', '45'])).
% 0.47/0.70  thf('47', plain,
% 0.47/0.70      (![X19 : $i, X20 : $i]:
% 0.47/0.70         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.70  thf('48', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.70  thf('49', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.47/0.70          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.70  thf('50', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.70          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['34'])).
% 0.47/0.70  thf('51', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.47/0.70          | ~ (v1_relat_1 @ X0)
% 0.47/0.70          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['49', '50'])).
% 0.47/0.70  thf('52', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.70          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['51'])).
% 0.47/0.70  thf('53', plain,
% 0.47/0.70      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.47/0.70          (k2_relat_1 @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['17', '43', '44', '45'])).
% 0.47/0.70  thf('54', plain,
% 0.47/0.70      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.70        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['52', '53'])).
% 0.47/0.70  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.70  thf('57', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.70      inference('demod', [status(thm)], ['55', '56'])).
% 0.47/0.70  thf('58', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['54', '57'])).
% 0.47/0.70  thf('59', plain,
% 0.47/0.70      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.47/0.70      inference('demod', [status(thm)], ['46', '58'])).
% 0.47/0.70  thf('60', plain,
% 0.47/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.70         (((X24) != (k1_xboole_0))
% 0.47/0.70          | ((X25) = (k1_xboole_0))
% 0.47/0.70          | (v1_funct_2 @ X26 @ X25 @ X24)
% 0.47/0.70          | ((X26) != (k1_xboole_0))
% 0.47/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.70  thf('61', plain,
% 0.47/0.70      (![X25 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.47/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ k1_xboole_0)))
% 0.47/0.70          | (v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0)
% 0.47/0.70          | ((X25) = (k1_xboole_0)))),
% 0.47/0.70      inference('simplify', [status(thm)], ['60'])).
% 0.47/0.70  thf(t113_zfmisc_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.70       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.70  thf('62', plain,
% 0.47/0.70      (![X5 : $i, X6 : $i]:
% 0.47/0.70         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.70  thf('63', plain,
% 0.47/0.70      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['62'])).
% 0.47/0.70  thf('64', plain,
% 0.47/0.70      (![X25 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.70          | (v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0)
% 0.47/0.70          | ((X25) = (k1_xboole_0)))),
% 0.47/0.70      inference('demod', [status(thm)], ['61', '63'])).
% 0.47/0.70  thf('65', plain,
% 0.47/0.70      ((![X25 : $i]:
% 0.47/0.70          (((X25) = (k1_xboole_0))
% 0.47/0.70           | (v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0)))
% 0.47/0.70         <= ((![X25 : $i]:
% 0.47/0.70                (((X25) = (k1_xboole_0))
% 0.47/0.70                 | (v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0))))),
% 0.47/0.70      inference('split', [status(esa)], ['64'])).
% 0.47/0.70  thf('66', plain,
% 0.47/0.70      (![X19 : $i, X20 : $i]:
% 0.47/0.70         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.70  thf('67', plain,
% 0.47/0.70      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['62'])).
% 0.47/0.70  thf('68', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.47/0.70      inference('sup+', [status(thm)], ['66', '67'])).
% 0.47/0.70  thf('69', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X0 @ 
% 0.47/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['6', '9'])).
% 0.47/0.70  thf('70', plain,
% 0.47/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.70  thf('71', plain,
% 0.47/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.70  thf('72', plain,
% 0.47/0.70      ((~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('split', [status(esa)], ['64'])).
% 0.47/0.70  thf('73', plain,
% 0.47/0.70      ((![X0 : $i]:
% 0.47/0.70          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.70           | ~ (v1_xboole_0 @ X0)))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['71', '72'])).
% 0.47/0.70  thf('74', plain,
% 0.47/0.70      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['62'])).
% 0.47/0.70  thf('75', plain,
% 0.47/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.70         (~ (v1_xboole_0 @ X7)
% 0.47/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 0.47/0.70          | (v1_xboole_0 @ X8))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.47/0.70  thf('76', plain,
% 0.47/0.70      (![X1 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.70          | (v1_xboole_0 @ X1)
% 0.47/0.70          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['74', '75'])).
% 0.47/0.70  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.70  thf('78', plain,
% 0.47/0.70      (![X1 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.70          | (v1_xboole_0 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['76', '77'])).
% 0.47/0.70  thf('79', plain,
% 0.47/0.70      ((![X0 : $i]: ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('clc', [status(thm)], ['73', '78'])).
% 0.47/0.70  thf('80', plain,
% 0.47/0.70      ((![X0 : $i, X1 : $i]:
% 0.47/0.70          (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['70', '79'])).
% 0.47/0.70  thf('81', plain,
% 0.47/0.70      ((![X0 : $i]:
% 0.47/0.70          (~ (v1_relat_1 @ X0)
% 0.47/0.70           | ~ (v1_xboole_0 @ 
% 0.47/0.70                (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['69', '80'])).
% 0.47/0.70  thf('82', plain,
% 0.47/0.70      ((![X0 : $i, X1 : $i]:
% 0.47/0.70          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.70           | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 0.47/0.70           | ~ (v1_relat_1 @ X0)))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['68', '81'])).
% 0.47/0.70  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.70  thf('84', plain,
% 0.47/0.70      ((![X0 : $i, X1 : $i]:
% 0.47/0.70          ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1) | ~ (v1_relat_1 @ X0)))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.70  thf('85', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.70  thf('86', plain,
% 0.47/0.70      ((![X0 : $i]:
% 0.47/0.70          (~ (v1_relat_1 @ X0)
% 0.47/0.70           | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70           | ~ (v1_relat_1 @ X0)))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['84', '85'])).
% 0.47/0.70  thf('87', plain,
% 0.47/0.70      ((![X0 : $i]:
% 0.47/0.70          ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70           | ~ (v1_relat_1 @ X0)))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('simplify', [status(thm)], ['86'])).
% 0.47/0.70  thf('88', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.70          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['34'])).
% 0.47/0.70  thf('89', plain,
% 0.47/0.70      ((![X0 : $i]:
% 0.47/0.70          (~ (v1_relat_1 @ X0)
% 0.47/0.70           | ~ (v1_relat_1 @ X0)
% 0.47/0.70           | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.70  thf('90', plain,
% 0.47/0.70      ((![X0 : $i]:
% 0.47/0.70          ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.70           | ~ (v1_relat_1 @ X0)))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('simplify', [status(thm)], ['89'])).
% 0.47/0.70  thf('91', plain,
% 0.47/0.70      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.47/0.70  thf('92', plain,
% 0.47/0.70      ((~ (v1_relat_1 @ sk_A))
% 0.47/0.70         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['90', '91'])).
% 0.47/0.70  thf('93', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('94', plain,
% 0.47/0.70      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.47/0.70      inference('demod', [status(thm)], ['92', '93'])).
% 0.47/0.70  thf('95', plain,
% 0.47/0.70      ((![X25 : $i]:
% 0.47/0.70          (((X25) = (k1_xboole_0))
% 0.47/0.70           | (v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0))) | 
% 0.47/0.70       ~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.47/0.70      inference('split', [status(esa)], ['64'])).
% 0.47/0.70  thf('96', plain,
% 0.47/0.70      ((![X25 : $i]:
% 0.47/0.70          (((X25) = (k1_xboole_0))
% 0.47/0.70           | (v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0)))),
% 0.47/0.70      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 0.47/0.70  thf('97', plain,
% 0.47/0.70      (![X25 : $i]:
% 0.47/0.70         (((X25) = (k1_xboole_0))
% 0.47/0.70          | (v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0))),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['65', '96'])).
% 0.47/0.70  thf('98', plain,
% 0.47/0.70      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.47/0.70      inference('demod', [status(thm)], ['46', '58'])).
% 0.47/0.70  thf('99', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['97', '98'])).
% 0.47/0.70  thf('100', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('demod', [status(thm)], ['59', '99'])).
% 0.47/0.70  thf('101', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['54', '57'])).
% 0.47/0.70  thf('102', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X0 @ 
% 0.47/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['6', '9'])).
% 0.47/0.70  thf('103', plain,
% 0.47/0.70      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.47/0.70         (k1_zfmisc_1 @ 
% 0.47/0.70          (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)))
% 0.47/0.70        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['101', '102'])).
% 0.47/0.70  thf('104', plain,
% 0.47/0.70      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['62'])).
% 0.47/0.70  thf('105', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.70      inference('demod', [status(thm)], ['55', '56'])).
% 0.47/0.70  thf('106', plain,
% 0.47/0.70      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.47/0.70  thf('107', plain,
% 0.47/0.70      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['62'])).
% 0.47/0.70  thf('108', plain,
% 0.47/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.70         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.47/0.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.70  thf('109', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.70          | ((k1_relset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_relat_1 @ X1)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['107', '108'])).
% 0.47/0.70  thf('110', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.70           = (k1_relat_1 @ k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['106', '109'])).
% 0.47/0.70  thf('111', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['97', '98'])).
% 0.47/0.70  thf('112', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['110', '111'])).
% 0.47/0.70  thf('113', plain,
% 0.47/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.70         (((X21) != (k1_relset_1 @ X21 @ X22 @ X23))
% 0.47/0.70          | (v1_funct_2 @ X23 @ X21 @ X22)
% 0.47/0.70          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.70  thf('114', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (((X0) != (k1_xboole_0))
% 0.47/0.70          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.47/0.70          | (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['112', '113'])).
% 0.47/0.70  thf('115', plain,
% 0.47/0.70      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.70        | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['114'])).
% 0.47/0.70  thf('116', plain,
% 0.47/0.70      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.47/0.70  thf('117', plain,
% 0.47/0.70      (![X5 : $i, X6 : $i]:
% 0.47/0.70         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.70  thf('118', plain,
% 0.47/0.70      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['117'])).
% 0.47/0.70  thf('119', plain,
% 0.47/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.70         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.47/0.70          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.47/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.70  thf('120', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.70          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.47/0.70          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['118', '119'])).
% 0.47/0.70  thf('121', plain,
% 0.47/0.70      (![X19 : $i, X20 : $i]:
% 0.47/0.70         ((zip_tseitin_0 @ X19 @ X20) | ((X20) != (k1_xboole_0)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.70  thf('122', plain, (![X19 : $i]: (zip_tseitin_0 @ X19 @ k1_xboole_0)),
% 0.47/0.70      inference('simplify', [status(thm)], ['121'])).
% 0.47/0.70  thf('123', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.70          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['120', '122'])).
% 0.47/0.70  thf('124', plain,
% 0.47/0.70      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.47/0.70      inference('sup-', [status(thm)], ['116', '123'])).
% 0.47/0.70  thf('125', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('simplify_reflect+', [status(thm)], ['115', '124'])).
% 0.47/0.70  thf('126', plain, ($false), inference('demod', [status(thm)], ['100', '125'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
