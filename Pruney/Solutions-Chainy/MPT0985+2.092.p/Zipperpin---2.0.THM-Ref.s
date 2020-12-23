%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fXdGnfyy7b

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:39 EST 2020

% Result     : Theorem 5.22s
% Output     : Refutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :  293 (15786 expanded)
%              Number of leaves         :   37 (4589 expanded)
%              Depth                    :   34
%              Number of atoms          : 2263 (268108 expanded)
%              Number of equality atoms :  124 (9369 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf(zf_stmt_0,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 != k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ( X34 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('2',plain,(
    ! [X33: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X33 @ k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('4',plain,(
    ! [X33: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X33 @ k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X18 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('14',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X18 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('28',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ X36 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('45',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('46',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('47',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ X36 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['43','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('61',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('65',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['59','62','63','64'])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('71',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['38','67','68','69','70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('75',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('78',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('79',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('81',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['78'])).

thf('83',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['78'])).

thf('89',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('91',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('92',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('95',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('96',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('98',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('101',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('102',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('103',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('104',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('105',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( v1_funct_2 @ X35 @ ( k1_relat_1 @ X35 ) @ X36 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['101','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['99','113'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['41','42'])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('119',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['78'])).

thf('121',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['88','121'])).

thf('123',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('124',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('125',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('126',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('127',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('128',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('129',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( v1_funct_2 @ X35 @ ( k1_relat_1 @ X35 ) @ X36 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('135',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['126','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('140',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['125','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('145',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['124','145'])).

thf('147',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['41','42'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('150',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('151',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['146','147','148','149','150'])).

thf('152',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['123','151'])).

thf('153',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['122','152'])).

thf('154',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['78'])).

thf('155',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['87','153','154'])).

thf('156',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['79','155'])).

thf('157',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('159',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['41','42'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('163',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('164',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['159','160','161','162','163'])).

thf('165',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['79','155'])).

thf('166',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['156','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['76','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['24','169'])).

thf('171',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['41','42'])).

thf('172',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['164','165'])).

thf('173',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('175',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('176',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('177',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['170','173','174','175','176'])).

thf('178',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('179',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['177','180'])).

thf('182',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','181'])).

thf('183',plain,(
    m1_subset_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','182'])).

thf('184',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','181'])).

thf('185',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','181'])).

thf('186',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['156','166'])).

thf('187',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('188',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['164','165'])).

thf('189',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 != k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('191',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['189','191'])).

thf('193',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('194',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['164','165'])).

thf('195',plain,(
    v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['192','195'])).

thf('197',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('198',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['164','165'])).

thf('199',plain,
    ( ( k1_relset_1 @ sk_A @ k1_xboole_0 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( k1_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['196','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','20'])).

thf('202',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('204',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['164','165'])).

thf('205',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('207',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['164','165'])).

thf('208',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['164','165'])).

thf('209',plain,
    ( ( zip_tseitin_1 @ sk_C @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['170','173','174','175','176'])).

thf('211',plain,(
    zip_tseitin_1 @ sk_C @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['205','211'])).

thf('213',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['202','212'])).

thf('214',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['186','214'])).

thf('216',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('217',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['41','42'])).

thf('218',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ X36 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('221',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['216','222'])).

thf('224',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['164','165'])).

thf('225',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('227',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['41','42'])).

thf('229',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( v1_funct_2 @ X35 @ ( k1_relat_1 @ X35 ) @ X36 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('233',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['230','231','232'])).

thf('234',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['164','165'])).

thf('235',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('236',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ X0 ) ),
    inference(demod,[status(thm)],['233','234','235'])).

thf('237',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['227','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('239',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ k1_xboole_0 ) ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['237','238'])).

thf('240',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['171','172'])).

thf('241',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('242',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('243',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('244',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['239','240','241','242','243'])).

thf('245',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['186','214'])).

thf('246',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['215','246'])).

thf('248',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','181'])).

thf('249',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','181'])).

thf('250',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','181'])).

thf('251',plain,(
    ~ ( m1_subset_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['247','248','249','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ~ ( m1_subset_1 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['185','251'])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( m1_subset_1 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['184','252'])).

thf('254',plain,(
    $false ),
    inference('sup-',[status(thm)],['183','253'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fXdGnfyy7b
% 0.13/0.37  % Computer   : n002.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:12:37 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 5.22/5.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.22/5.45  % Solved by: fo/fo7.sh
% 5.22/5.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.22/5.45  % done 3824 iterations in 4.958s
% 5.22/5.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.22/5.45  % SZS output start Refutation
% 5.22/5.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.22/5.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.22/5.45  thf(sk_A_type, type, sk_A: $i).
% 5.22/5.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.22/5.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.22/5.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.22/5.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.22/5.45  thf(sk_B_type, type, sk_B: $i).
% 5.22/5.45  thf(sk_C_type, type, sk_C: $i).
% 5.22/5.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.22/5.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.22/5.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.22/5.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.22/5.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.22/5.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.22/5.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.22/5.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.22/5.45  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.22/5.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.22/5.45  thf(t4_subset_1, axiom,
% 5.22/5.45    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.22/5.45  thf('0', plain,
% 5.22/5.45      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 5.22/5.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.22/5.45  thf(d1_funct_2, axiom,
% 5.22/5.45    (![A:$i,B:$i,C:$i]:
% 5.22/5.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.22/5.45       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.22/5.45           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.22/5.45             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.22/5.45         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.22/5.45           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.22/5.45             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.22/5.45  thf(zf_stmt_0, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.22/5.45  thf(zf_stmt_1, axiom,
% 5.22/5.45    (![C:$i,B:$i,A:$i]:
% 5.22/5.45     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.22/5.45       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.22/5.45  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $o).
% 5.22/5.45  thf(zf_stmt_3, axiom,
% 5.22/5.45    (![B:$i,A:$i]:
% 5.22/5.45     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.22/5.45       ( zip_tseitin_0 @ B @ A ) ))).
% 5.22/5.45  thf(zf_stmt_4, axiom,
% 5.22/5.45    (![A:$i,B:$i,C:$i]:
% 5.22/5.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.22/5.45       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.22/5.45         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.22/5.45           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.22/5.45             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.22/5.45  thf('1', plain,
% 5.22/5.45      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.22/5.45         (((X32) != (k1_xboole_0))
% 5.22/5.45          | ((X33) = (k1_xboole_0))
% 5.22/5.45          | (v1_funct_2 @ X34 @ X33 @ X32)
% 5.22/5.45          | ((X34) != (k1_xboole_0))
% 5.22/5.45          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.22/5.45  thf('2', plain,
% 5.22/5.45      (![X33 : $i]:
% 5.22/5.45         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 5.22/5.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ k1_xboole_0)))
% 5.22/5.45          | (v1_funct_2 @ k1_xboole_0 @ X33 @ k1_xboole_0)
% 5.22/5.45          | ((X33) = (k1_xboole_0)))),
% 5.22/5.45      inference('simplify', [status(thm)], ['1'])).
% 5.22/5.45  thf('3', plain,
% 5.22/5.45      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 5.22/5.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.22/5.45  thf('4', plain,
% 5.22/5.45      (![X33 : $i]:
% 5.22/5.45         ((v1_funct_2 @ k1_xboole_0 @ X33 @ k1_xboole_0)
% 5.22/5.45          | ((X33) = (k1_xboole_0)))),
% 5.22/5.45      inference('demod', [status(thm)], ['2', '3'])).
% 5.22/5.45  thf('5', plain,
% 5.22/5.45      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.22/5.45         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 5.22/5.45          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 5.22/5.45          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.22/5.45  thf('6', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (((X0) = (k1_xboole_0))
% 5.22/5.45          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 5.22/5.45          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 5.22/5.45      inference('sup-', [status(thm)], ['4', '5'])).
% 5.22/5.45  thf('7', plain,
% 5.22/5.45      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 5.22/5.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.22/5.45  thf(redefinition_k1_relset_1, axiom,
% 5.22/5.45    (![A:$i,B:$i,C:$i]:
% 5.22/5.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.22/5.45       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.22/5.45  thf('8', plain,
% 5.22/5.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 5.22/5.45         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 5.22/5.45          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 5.22/5.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.22/5.45  thf('9', plain,
% 5.22/5.45      (![X0 : $i, X1 : $i]:
% 5.22/5.45         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 5.22/5.45      inference('sup-', [status(thm)], ['7', '8'])).
% 5.22/5.45  thf('10', plain,
% 5.22/5.45      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 5.22/5.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.22/5.45  thf(dt_k1_relset_1, axiom,
% 5.22/5.45    (![A:$i,B:$i,C:$i]:
% 5.22/5.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.22/5.45       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.22/5.45  thf('11', plain,
% 5.22/5.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.22/5.45         ((m1_subset_1 @ (k1_relset_1 @ X18 @ X19 @ X20) @ (k1_zfmisc_1 @ X18))
% 5.22/5.45          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 5.22/5.45      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 5.22/5.45  thf('12', plain,
% 5.22/5.45      (![X0 : $i, X1 : $i]:
% 5.22/5.45         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 5.22/5.45          (k1_zfmisc_1 @ X1))),
% 5.22/5.45      inference('sup-', [status(thm)], ['10', '11'])).
% 5.22/5.45  thf('13', plain,
% 5.22/5.45      (![X0 : $i, X1 : $i]:
% 5.22/5.45         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 5.22/5.45      inference('sup-', [status(thm)], ['7', '8'])).
% 5.22/5.45  thf('14', plain,
% 5.22/5.45      (![X1 : $i]:
% 5.22/5.45         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X1))),
% 5.22/5.45      inference('demod', [status(thm)], ['12', '13'])).
% 5.22/5.45  thf(t3_subset, axiom,
% 5.22/5.45    (![A:$i,B:$i]:
% 5.22/5.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.22/5.45  thf('15', plain,
% 5.22/5.45      (![X5 : $i, X6 : $i]:
% 5.22/5.45         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 5.22/5.45      inference('cnf', [status(esa)], [t3_subset])).
% 5.22/5.45  thf('16', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 5.22/5.45      inference('sup-', [status(thm)], ['14', '15'])).
% 5.22/5.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.22/5.45  thf('17', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.22/5.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.22/5.45  thf(d10_xboole_0, axiom,
% 5.22/5.45    (![A:$i,B:$i]:
% 5.22/5.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.22/5.45  thf('18', plain,
% 5.22/5.45      (![X0 : $i, X2 : $i]:
% 5.22/5.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.22/5.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.22/5.45  thf('19', plain,
% 5.22/5.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.22/5.45      inference('sup-', [status(thm)], ['17', '18'])).
% 5.22/5.45  thf('20', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.22/5.45      inference('sup-', [status(thm)], ['16', '19'])).
% 5.22/5.45  thf('21', plain,
% 5.22/5.45      (![X0 : $i, X1 : $i]:
% 5.22/5.45         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.22/5.45      inference('demod', [status(thm)], ['9', '20'])).
% 5.22/5.45  thf('22', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (((X0) = (k1_xboole_0))
% 5.22/5.45          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 5.22/5.45          | ((X0) = (k1_xboole_0)))),
% 5.22/5.45      inference('demod', [status(thm)], ['6', '21'])).
% 5.22/5.45  thf('23', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 5.22/5.45          | ((X0) = (k1_xboole_0)))),
% 5.22/5.45      inference('simplify', [status(thm)], ['22'])).
% 5.22/5.45  thf(t55_funct_1, axiom,
% 5.22/5.45    (![A:$i]:
% 5.22/5.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.22/5.45       ( ( v2_funct_1 @ A ) =>
% 5.22/5.45         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 5.22/5.45           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.22/5.45  thf('24', plain,
% 5.22/5.45      (![X14 : $i]:
% 5.22/5.45         (~ (v2_funct_1 @ X14)
% 5.22/5.45          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 5.22/5.45          | ~ (v1_funct_1 @ X14)
% 5.22/5.45          | ~ (v1_relat_1 @ X14))),
% 5.22/5.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.22/5.45  thf(fc6_funct_1, axiom,
% 5.22/5.45    (![A:$i]:
% 5.22/5.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 5.22/5.45       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 5.22/5.45         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 5.22/5.45         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 5.22/5.45  thf('25', plain,
% 5.22/5.45      (![X13 : $i]:
% 5.22/5.45         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 5.22/5.45          | ~ (v2_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_relat_1 @ X13))),
% 5.22/5.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.22/5.45  thf(t31_funct_2, conjecture,
% 5.22/5.45    (![A:$i,B:$i,C:$i]:
% 5.22/5.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.22/5.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.22/5.45       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 5.22/5.45         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 5.22/5.45           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 5.22/5.45           ( m1_subset_1 @
% 5.22/5.45             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 5.22/5.45  thf(zf_stmt_5, negated_conjecture,
% 5.22/5.45    (~( ![A:$i,B:$i,C:$i]:
% 5.22/5.45        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.22/5.45            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.22/5.45          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 5.22/5.45            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 5.22/5.45              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 5.22/5.45              ( m1_subset_1 @
% 5.22/5.45                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 5.22/5.45    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 5.22/5.45  thf('26', plain,
% 5.22/5.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('27', plain,
% 5.22/5.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.22/5.45         ((m1_subset_1 @ (k1_relset_1 @ X18 @ X19 @ X20) @ (k1_zfmisc_1 @ X18))
% 5.22/5.45          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 5.22/5.45      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 5.22/5.45  thf('28', plain,
% 5.22/5.45      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 5.22/5.45      inference('sup-', [status(thm)], ['26', '27'])).
% 5.22/5.45  thf('29', plain,
% 5.22/5.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('30', plain,
% 5.22/5.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 5.22/5.45         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 5.22/5.45          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 5.22/5.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.22/5.45  thf('31', plain,
% 5.22/5.45      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 5.22/5.45      inference('sup-', [status(thm)], ['29', '30'])).
% 5.22/5.45  thf('32', plain,
% 5.22/5.45      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 5.22/5.45      inference('demod', [status(thm)], ['28', '31'])).
% 5.22/5.45  thf('33', plain,
% 5.22/5.45      (![X5 : $i, X6 : $i]:
% 5.22/5.45         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 5.22/5.45      inference('cnf', [status(esa)], [t3_subset])).
% 5.22/5.45  thf('34', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 5.22/5.45      inference('sup-', [status(thm)], ['32', '33'])).
% 5.22/5.45  thf('35', plain,
% 5.22/5.45      (![X14 : $i]:
% 5.22/5.45         (~ (v2_funct_1 @ X14)
% 5.22/5.45          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 5.22/5.45          | ~ (v1_funct_1 @ X14)
% 5.22/5.45          | ~ (v1_relat_1 @ X14))),
% 5.22/5.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.22/5.45  thf(t4_funct_2, axiom,
% 5.22/5.45    (![A:$i,B:$i]:
% 5.22/5.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.22/5.45       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 5.22/5.45         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 5.22/5.45           ( m1_subset_1 @
% 5.22/5.45             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 5.22/5.45  thf('36', plain,
% 5.22/5.45      (![X35 : $i, X36 : $i]:
% 5.22/5.45         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 5.22/5.45          | (m1_subset_1 @ X35 @ 
% 5.22/5.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ X36)))
% 5.22/5.45          | ~ (v1_funct_1 @ X35)
% 5.22/5.45          | ~ (v1_relat_1 @ X35))),
% 5.22/5.45      inference('cnf', [status(esa)], [t4_funct_2])).
% 5.22/5.45  thf('37', plain,
% 5.22/5.45      (![X0 : $i, X1 : $i]:
% 5.22/5.45         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.22/5.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.22/5.45          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.22/5.45             (k1_zfmisc_1 @ 
% 5.22/5.45              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 5.22/5.45      inference('sup-', [status(thm)], ['35', '36'])).
% 5.22/5.45  thf('38', plain,
% 5.22/5.45      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45         (k1_zfmisc_1 @ 
% 5.22/5.45          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 5.22/5.45        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.22/5.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 5.22/5.45        | ~ (v2_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v1_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v1_relat_1 @ sk_C))),
% 5.22/5.45      inference('sup-', [status(thm)], ['34', '37'])).
% 5.22/5.45  thf('39', plain,
% 5.22/5.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf(redefinition_k2_relset_1, axiom,
% 5.22/5.45    (![A:$i,B:$i,C:$i]:
% 5.22/5.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.22/5.45       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.22/5.45  thf('40', plain,
% 5.22/5.45      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.22/5.45         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 5.22/5.45          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 5.22/5.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.22/5.45  thf('41', plain,
% 5.22/5.45      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 5.22/5.45      inference('sup-', [status(thm)], ['39', '40'])).
% 5.22/5.45  thf('42', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('43', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.22/5.45      inference('sup+', [status(thm)], ['41', '42'])).
% 5.22/5.45  thf('44', plain,
% 5.22/5.45      (![X14 : $i]:
% 5.22/5.45         (~ (v2_funct_1 @ X14)
% 5.22/5.45          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 5.22/5.45          | ~ (v1_funct_1 @ X14)
% 5.22/5.45          | ~ (v1_relat_1 @ X14))),
% 5.22/5.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.22/5.45  thf('45', plain,
% 5.22/5.45      (![X13 : $i]:
% 5.22/5.45         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 5.22/5.45          | ~ (v2_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_relat_1 @ X13))),
% 5.22/5.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.22/5.45  thf('46', plain,
% 5.22/5.45      (![X13 : $i]:
% 5.22/5.45         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 5.22/5.45          | ~ (v2_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_relat_1 @ X13))),
% 5.22/5.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.22/5.45  thf('47', plain,
% 5.22/5.45      (![X14 : $i]:
% 5.22/5.45         (~ (v2_funct_1 @ X14)
% 5.22/5.45          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 5.22/5.45          | ~ (v1_funct_1 @ X14)
% 5.22/5.45          | ~ (v1_relat_1 @ X14))),
% 5.22/5.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.22/5.45  thf('48', plain,
% 5.22/5.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.22/5.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.22/5.45  thf('49', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.22/5.45      inference('simplify', [status(thm)], ['48'])).
% 5.22/5.45  thf('50', plain,
% 5.22/5.45      (![X35 : $i, X36 : $i]:
% 5.22/5.45         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 5.22/5.45          | (m1_subset_1 @ X35 @ 
% 5.22/5.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ X36)))
% 5.22/5.45          | ~ (v1_funct_1 @ X35)
% 5.22/5.45          | ~ (v1_relat_1 @ X35))),
% 5.22/5.45      inference('cnf', [status(esa)], [t4_funct_2])).
% 5.22/5.45  thf('51', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | (m1_subset_1 @ X0 @ 
% 5.22/5.45             (k1_zfmisc_1 @ 
% 5.22/5.45              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 5.22/5.45      inference('sup-', [status(thm)], ['49', '50'])).
% 5.22/5.45  thf('52', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.22/5.45           (k1_zfmisc_1 @ 
% 5.22/5.45            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.22/5.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 5.22/5.45      inference('sup+', [status(thm)], ['47', '51'])).
% 5.22/5.45  thf('53', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.22/5.45             (k1_zfmisc_1 @ 
% 5.22/5.45              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 5.22/5.45               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 5.22/5.45      inference('sup-', [status(thm)], ['46', '52'])).
% 5.22/5.45  thf('54', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.22/5.45           (k1_zfmisc_1 @ 
% 5.22/5.45            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 5.22/5.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0))),
% 5.22/5.45      inference('simplify', [status(thm)], ['53'])).
% 5.22/5.45  thf('55', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.22/5.45             (k1_zfmisc_1 @ 
% 5.22/5.45              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 5.22/5.45               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 5.22/5.45      inference('sup-', [status(thm)], ['45', '54'])).
% 5.22/5.45  thf('56', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.22/5.45           (k1_zfmisc_1 @ 
% 5.22/5.45            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0))),
% 5.22/5.45      inference('simplify', [status(thm)], ['55'])).
% 5.22/5.45  thf('57', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.22/5.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0))),
% 5.22/5.45      inference('sup+', [status(thm)], ['44', '56'])).
% 5.22/5.45  thf('58', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.22/5.45             (k1_zfmisc_1 @ 
% 5.22/5.45              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 5.22/5.45      inference('simplify', [status(thm)], ['57'])).
% 5.22/5.45  thf('59', plain,
% 5.22/5.45      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 5.22/5.45        | ~ (v1_relat_1 @ sk_C)
% 5.22/5.45        | ~ (v1_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v2_funct_1 @ sk_C))),
% 5.22/5.45      inference('sup+', [status(thm)], ['43', '58'])).
% 5.22/5.45  thf('60', plain,
% 5.22/5.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf(cc1_relset_1, axiom,
% 5.22/5.45    (![A:$i,B:$i,C:$i]:
% 5.22/5.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.22/5.45       ( v1_relat_1 @ C ) ))).
% 5.22/5.45  thf('61', plain,
% 5.22/5.45      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.22/5.45         ((v1_relat_1 @ X15)
% 5.22/5.45          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 5.22/5.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.22/5.45  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.45      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.45  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('64', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('65', plain,
% 5.22/5.45      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 5.22/5.45      inference('demod', [status(thm)], ['59', '62', '63', '64'])).
% 5.22/5.45  thf('66', plain,
% 5.22/5.45      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.22/5.45         ((v1_relat_1 @ X15)
% 5.22/5.45          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 5.22/5.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.22/5.45  thf('67', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 5.22/5.45      inference('sup-', [status(thm)], ['65', '66'])).
% 5.22/5.45  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.45      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.45  thf('71', plain,
% 5.22/5.45      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45         (k1_zfmisc_1 @ 
% 5.22/5.45          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 5.22/5.45        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.22/5.45      inference('demod', [status(thm)], ['38', '67', '68', '69', '70'])).
% 5.22/5.45  thf('72', plain,
% 5.22/5.45      ((~ (v1_relat_1 @ sk_C)
% 5.22/5.45        | ~ (v1_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v2_funct_1 @ sk_C)
% 5.22/5.45        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45           (k1_zfmisc_1 @ 
% 5.22/5.45            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 5.22/5.45      inference('sup-', [status(thm)], ['25', '71'])).
% 5.22/5.45  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.45      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.45  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('75', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('76', plain,
% 5.22/5.45      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45        (k1_zfmisc_1 @ 
% 5.22/5.45         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 5.22/5.45      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 5.22/5.45  thf('77', plain,
% 5.22/5.45      (![X27 : $i, X28 : $i]:
% 5.22/5.45         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.22/5.45  thf('78', plain,
% 5.22/5.45      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.22/5.45        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 5.22/5.45        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('79', plain,
% 5.22/5.45      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 5.22/5.45         <= (~
% 5.22/5.45             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 5.22/5.45      inference('split', [status(esa)], ['78'])).
% 5.22/5.45  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.45      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.45  thf('81', plain,
% 5.22/5.45      (![X13 : $i]:
% 5.22/5.45         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 5.22/5.45          | ~ (v2_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_relat_1 @ X13))),
% 5.22/5.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.22/5.45  thf('82', plain,
% 5.22/5.45      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.22/5.45         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.22/5.45      inference('split', [status(esa)], ['78'])).
% 5.22/5.45  thf('83', plain,
% 5.22/5.45      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C)))
% 5.22/5.45         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.22/5.45      inference('sup-', [status(thm)], ['81', '82'])).
% 5.22/5.45  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('86', plain,
% 5.22/5.45      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.22/5.45      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.22/5.45  thf('87', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.22/5.45      inference('sup-', [status(thm)], ['80', '86'])).
% 5.22/5.45  thf('88', plain,
% 5.22/5.45      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 5.22/5.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.22/5.45      inference('split', [status(esa)], ['78'])).
% 5.22/5.45  thf('89', plain,
% 5.22/5.45      (![X27 : $i, X28 : $i]:
% 5.22/5.45         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.22/5.45  thf('90', plain,
% 5.22/5.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('91', plain,
% 5.22/5.45      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.22/5.45         (~ (zip_tseitin_0 @ X32 @ X33)
% 5.22/5.45          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 5.22/5.45          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.22/5.45  thf('92', plain,
% 5.22/5.45      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.22/5.45      inference('sup-', [status(thm)], ['90', '91'])).
% 5.22/5.45  thf('93', plain,
% 5.22/5.45      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 5.22/5.45      inference('sup-', [status(thm)], ['89', '92'])).
% 5.22/5.45  thf('94', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('95', plain,
% 5.22/5.45      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.22/5.45         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 5.22/5.45          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 5.22/5.45          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.22/5.45  thf('96', plain,
% 5.22/5.45      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 5.22/5.45        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 5.22/5.45      inference('sup-', [status(thm)], ['94', '95'])).
% 5.22/5.45  thf('97', plain,
% 5.22/5.45      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 5.22/5.45      inference('sup-', [status(thm)], ['29', '30'])).
% 5.22/5.45  thf('98', plain,
% 5.22/5.45      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.22/5.45      inference('demod', [status(thm)], ['96', '97'])).
% 5.22/5.45  thf('99', plain,
% 5.22/5.45      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.22/5.45      inference('sup-', [status(thm)], ['93', '98'])).
% 5.22/5.45  thf('100', plain,
% 5.22/5.45      (![X14 : $i]:
% 5.22/5.45         (~ (v2_funct_1 @ X14)
% 5.22/5.45          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 5.22/5.45          | ~ (v1_funct_1 @ X14)
% 5.22/5.45          | ~ (v1_relat_1 @ X14))),
% 5.22/5.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.22/5.45  thf('101', plain,
% 5.22/5.45      (![X13 : $i]:
% 5.22/5.45         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 5.22/5.45          | ~ (v2_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_relat_1 @ X13))),
% 5.22/5.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.22/5.45  thf('102', plain,
% 5.22/5.45      (![X13 : $i]:
% 5.22/5.45         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 5.22/5.45          | ~ (v2_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_relat_1 @ X13))),
% 5.22/5.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.22/5.45  thf('103', plain,
% 5.22/5.45      (![X14 : $i]:
% 5.22/5.45         (~ (v2_funct_1 @ X14)
% 5.22/5.45          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 5.22/5.45          | ~ (v1_funct_1 @ X14)
% 5.22/5.45          | ~ (v1_relat_1 @ X14))),
% 5.22/5.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.22/5.45  thf('104', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.22/5.45      inference('simplify', [status(thm)], ['48'])).
% 5.22/5.45  thf('105', plain,
% 5.22/5.45      (![X35 : $i, X36 : $i]:
% 5.22/5.45         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 5.22/5.45          | (v1_funct_2 @ X35 @ (k1_relat_1 @ X35) @ X36)
% 5.22/5.45          | ~ (v1_funct_1 @ X35)
% 5.22/5.45          | ~ (v1_relat_1 @ X35))),
% 5.22/5.45      inference('cnf', [status(esa)], [t4_funct_2])).
% 5.22/5.45  thf('106', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 5.22/5.45      inference('sup-', [status(thm)], ['104', '105'])).
% 5.22/5.45  thf('107', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.22/5.45           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.22/5.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 5.22/5.45      inference('sup+', [status(thm)], ['103', '106'])).
% 5.22/5.45  thf('108', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.22/5.45             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 5.22/5.45      inference('sup-', [status(thm)], ['102', '107'])).
% 5.22/5.45  thf('109', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.22/5.45           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.22/5.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0))),
% 5.22/5.45      inference('simplify', [status(thm)], ['108'])).
% 5.22/5.45  thf('110', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.22/5.45             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 5.22/5.45      inference('sup-', [status(thm)], ['101', '109'])).
% 5.22/5.45  thf('111', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.22/5.45           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0))),
% 5.22/5.45      inference('simplify', [status(thm)], ['110'])).
% 5.22/5.45  thf('112', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.22/5.45           (k1_relat_1 @ X0))
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0))),
% 5.22/5.45      inference('sup+', [status(thm)], ['100', '111'])).
% 5.22/5.45  thf('113', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.22/5.45             (k1_relat_1 @ X0)))),
% 5.22/5.45      inference('simplify', [status(thm)], ['112'])).
% 5.22/5.45  thf('114', plain,
% 5.22/5.45      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 5.22/5.45        | ((sk_B) = (k1_xboole_0))
% 5.22/5.45        | ~ (v1_relat_1 @ sk_C)
% 5.22/5.45        | ~ (v1_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v2_funct_1 @ sk_C))),
% 5.22/5.45      inference('sup+', [status(thm)], ['99', '113'])).
% 5.22/5.45  thf('115', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.22/5.45      inference('sup+', [status(thm)], ['41', '42'])).
% 5.22/5.45  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.45      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.45  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('119', plain,
% 5.22/5.45      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 5.22/5.45        | ((sk_B) = (k1_xboole_0)))),
% 5.22/5.45      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 5.22/5.45  thf('120', plain,
% 5.22/5.45      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 5.22/5.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.22/5.45      inference('split', [status(esa)], ['78'])).
% 5.22/5.45  thf('121', plain,
% 5.22/5.45      ((((sk_B) = (k1_xboole_0)))
% 5.22/5.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.22/5.45      inference('sup-', [status(thm)], ['119', '120'])).
% 5.22/5.45  thf('122', plain,
% 5.22/5.45      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 5.22/5.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.22/5.45      inference('demod', [status(thm)], ['88', '121'])).
% 5.22/5.45  thf('123', plain,
% 5.22/5.45      ((((sk_B) = (k1_xboole_0)))
% 5.22/5.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.22/5.45      inference('sup-', [status(thm)], ['119', '120'])).
% 5.22/5.45  thf('124', plain,
% 5.22/5.45      (![X14 : $i]:
% 5.22/5.45         (~ (v2_funct_1 @ X14)
% 5.22/5.45          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 5.22/5.45          | ~ (v1_funct_1 @ X14)
% 5.22/5.45          | ~ (v1_relat_1 @ X14))),
% 5.22/5.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.22/5.45  thf('125', plain,
% 5.22/5.45      (![X13 : $i]:
% 5.22/5.45         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 5.22/5.45          | ~ (v2_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_relat_1 @ X13))),
% 5.22/5.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.22/5.45  thf('126', plain,
% 5.22/5.45      (![X13 : $i]:
% 5.22/5.45         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 5.22/5.45          | ~ (v2_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_funct_1 @ X13)
% 5.22/5.45          | ~ (v1_relat_1 @ X13))),
% 5.22/5.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.22/5.45  thf('127', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 5.22/5.45      inference('sup-', [status(thm)], ['32', '33'])).
% 5.22/5.45  thf('128', plain,
% 5.22/5.45      (![X14 : $i]:
% 5.22/5.45         (~ (v2_funct_1 @ X14)
% 5.22/5.45          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 5.22/5.45          | ~ (v1_funct_1 @ X14)
% 5.22/5.45          | ~ (v1_relat_1 @ X14))),
% 5.22/5.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.22/5.45  thf('129', plain,
% 5.22/5.45      (![X35 : $i, X36 : $i]:
% 5.22/5.45         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 5.22/5.45          | (v1_funct_2 @ X35 @ (k1_relat_1 @ X35) @ X36)
% 5.22/5.45          | ~ (v1_funct_1 @ X35)
% 5.22/5.45          | ~ (v1_relat_1 @ X35))),
% 5.22/5.45      inference('cnf', [status(esa)], [t4_funct_2])).
% 5.22/5.45  thf('130', plain,
% 5.22/5.45      (![X0 : $i, X1 : $i]:
% 5.22/5.45         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.22/5.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.22/5.45          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 5.22/5.45             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 5.22/5.45      inference('sup-', [status(thm)], ['128', '129'])).
% 5.22/5.45  thf('131', plain,
% 5.22/5.45      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 5.22/5.45        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.22/5.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 5.22/5.45        | ~ (v2_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v1_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v1_relat_1 @ sk_C))),
% 5.22/5.45      inference('sup-', [status(thm)], ['127', '130'])).
% 5.22/5.45  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.45      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.45  thf('135', plain,
% 5.22/5.45      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 5.22/5.45        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.22/5.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.22/5.45      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 5.22/5.45  thf('136', plain,
% 5.22/5.45      ((~ (v1_relat_1 @ sk_C)
% 5.22/5.45        | ~ (v1_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v2_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 5.22/5.45        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 5.22/5.45      inference('sup-', [status(thm)], ['126', '135'])).
% 5.22/5.45  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.45      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.45  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('140', plain,
% 5.22/5.45      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 5.22/5.45        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 5.22/5.45      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 5.22/5.45  thf('141', plain,
% 5.22/5.45      ((~ (v1_relat_1 @ sk_C)
% 5.22/5.45        | ~ (v1_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v2_funct_1 @ sk_C)
% 5.22/5.45        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 5.22/5.45      inference('sup-', [status(thm)], ['125', '140'])).
% 5.22/5.45  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.45      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.45  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('145', plain,
% 5.22/5.45      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45        (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 5.22/5.45      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 5.22/5.45  thf('146', plain,
% 5.22/5.45      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 5.22/5.45        | ~ (v1_relat_1 @ sk_C)
% 5.22/5.45        | ~ (v1_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v2_funct_1 @ sk_C))),
% 5.22/5.45      inference('sup+', [status(thm)], ['124', '145'])).
% 5.22/5.45  thf('147', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.22/5.45      inference('sup+', [status(thm)], ['41', '42'])).
% 5.22/5.45  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.45      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.45  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('150', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('151', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 5.22/5.45      inference('demod', [status(thm)], ['146', '147', '148', '149', '150'])).
% 5.22/5.45  thf('152', plain,
% 5.22/5.45      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 5.22/5.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.22/5.45      inference('sup+', [status(thm)], ['123', '151'])).
% 5.22/5.45  thf('153', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 5.22/5.45      inference('demod', [status(thm)], ['122', '152'])).
% 5.22/5.45  thf('154', plain,
% 5.22/5.45      (~
% 5.22/5.45       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 5.22/5.45       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 5.22/5.45       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.22/5.45      inference('split', [status(esa)], ['78'])).
% 5.22/5.45  thf('155', plain,
% 5.22/5.45      (~
% 5.22/5.45       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 5.22/5.45      inference('sat_resolution*', [status(thm)], ['87', '153', '154'])).
% 5.22/5.45  thf('156', plain,
% 5.22/5.45      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.22/5.45      inference('simpl_trail', [status(thm)], ['79', '155'])).
% 5.22/5.45  thf('157', plain,
% 5.22/5.45      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.22/5.45      inference('sup-', [status(thm)], ['93', '98'])).
% 5.22/5.45  thf('158', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         (~ (v2_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_funct_1 @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ X0)
% 5.22/5.45          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.22/5.45             (k1_zfmisc_1 @ 
% 5.22/5.45              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 5.22/5.45      inference('simplify', [status(thm)], ['57'])).
% 5.22/5.45  thf('159', plain,
% 5.22/5.45      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 5.22/5.45        | ((sk_B) = (k1_xboole_0))
% 5.22/5.45        | ~ (v1_relat_1 @ sk_C)
% 5.22/5.45        | ~ (v1_funct_1 @ sk_C)
% 5.22/5.45        | ~ (v2_funct_1 @ sk_C))),
% 5.22/5.45      inference('sup+', [status(thm)], ['157', '158'])).
% 5.22/5.45  thf('160', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.22/5.45      inference('sup+', [status(thm)], ['41', '42'])).
% 5.22/5.45  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.45      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.45  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('163', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('164', plain,
% 5.22/5.45      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.22/5.45        | ((sk_B) = (k1_xboole_0)))),
% 5.22/5.45      inference('demod', [status(thm)], ['159', '160', '161', '162', '163'])).
% 5.22/5.45  thf('165', plain,
% 5.22/5.45      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.22/5.45      inference('simpl_trail', [status(thm)], ['79', '155'])).
% 5.22/5.45  thf('166', plain, (((sk_B) = (k1_xboole_0))),
% 5.22/5.45      inference('clc', [status(thm)], ['164', '165'])).
% 5.22/5.45  thf('167', plain,
% 5.22/5.45      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 5.22/5.45      inference('demod', [status(thm)], ['156', '166'])).
% 5.22/5.45  thf('168', plain,
% 5.22/5.45      (![X0 : $i, X1 : $i]:
% 5.22/5.45         (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 5.22/5.45          | (zip_tseitin_0 @ X0 @ X1))),
% 5.22/5.45      inference('sup-', [status(thm)], ['77', '167'])).
% 5.22/5.45  thf('169', plain,
% 5.22/5.45      (![X0 : $i]: (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)),
% 5.22/5.45      inference('sup-', [status(thm)], ['76', '168'])).
% 5.22/5.45  thf('170', plain,
% 5.22/5.45      (![X0 : $i]:
% 5.22/5.45         ((zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)
% 5.22/5.45          | ~ (v1_relat_1 @ sk_C)
% 5.22/5.45          | ~ (v1_funct_1 @ sk_C)
% 5.22/5.45          | ~ (v2_funct_1 @ sk_C))),
% 5.22/5.45      inference('sup+', [status(thm)], ['24', '169'])).
% 5.22/5.45  thf('171', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.22/5.45      inference('sup+', [status(thm)], ['41', '42'])).
% 5.22/5.45  thf('172', plain, (((sk_B) = (k1_xboole_0))),
% 5.22/5.45      inference('clc', [status(thm)], ['164', '165'])).
% 5.22/5.45  thf('173', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 5.22/5.45      inference('demod', [status(thm)], ['171', '172'])).
% 5.22/5.45  thf('174', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.45      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.45  thf('175', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('176', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('177', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 5.22/5.45      inference('demod', [status(thm)], ['170', '173', '174', '175', '176'])).
% 5.22/5.45  thf('178', plain,
% 5.22/5.45      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 5.22/5.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.22/5.45  thf('179', plain,
% 5.22/5.45      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.22/5.45         (~ (zip_tseitin_0 @ X32 @ X33)
% 5.22/5.45          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 5.22/5.45          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.22/5.45  thf('180', plain,
% 5.22/5.45      (![X0 : $i, X1 : $i]:
% 5.22/5.45         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 5.22/5.45      inference('sup-', [status(thm)], ['178', '179'])).
% 5.22/5.45  thf('181', plain,
% 5.22/5.45      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.22/5.45      inference('sup-', [status(thm)], ['177', '180'])).
% 5.22/5.45  thf('182', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 5.22/5.45      inference('demod', [status(thm)], ['23', '181'])).
% 5.22/5.45  thf('183', plain, ((m1_subset_1 @ k1_xboole_0 @ k1_xboole_0)),
% 5.22/5.45      inference('demod', [status(thm)], ['0', '182'])).
% 5.22/5.45  thf('184', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 5.22/5.45      inference('demod', [status(thm)], ['23', '181'])).
% 5.22/5.45  thf('185', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 5.22/5.45      inference('demod', [status(thm)], ['23', '181'])).
% 5.22/5.45  thf('186', plain,
% 5.22/5.45      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 5.22/5.45      inference('demod', [status(thm)], ['156', '166'])).
% 5.22/5.45  thf('187', plain,
% 5.22/5.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.22/5.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.45  thf('188', plain, (((sk_B) = (k1_xboole_0))),
% 5.22/5.45      inference('clc', [status(thm)], ['164', '165'])).
% 5.22/5.45  thf('189', plain,
% 5.22/5.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 5.22/5.45      inference('demod', [status(thm)], ['187', '188'])).
% 5.22/5.45  thf('190', plain,
% 5.22/5.45      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.22/5.45         (((X32) != (k1_xboole_0))
% 5.22/5.45          | ((X33) = (k1_xboole_0))
% 5.22/5.45          | ((X34) = (k1_xboole_0))
% 5.22/5.45          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 5.22/5.46          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 5.22/5.46      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.22/5.46  thf('191', plain,
% 5.22/5.46      (![X33 : $i, X34 : $i]:
% 5.22/5.46         (~ (m1_subset_1 @ X34 @ 
% 5.22/5.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ k1_xboole_0)))
% 5.22/5.46          | ~ (v1_funct_2 @ X34 @ X33 @ k1_xboole_0)
% 5.22/5.46          | ((X34) = (k1_xboole_0))
% 5.22/5.46          | ((X33) = (k1_xboole_0)))),
% 5.22/5.46      inference('simplify', [status(thm)], ['190'])).
% 5.22/5.46  thf('192', plain,
% 5.22/5.46      ((((sk_A) = (k1_xboole_0))
% 5.22/5.46        | ((sk_C) = (k1_xboole_0))
% 5.22/5.46        | ~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0))),
% 5.22/5.46      inference('sup-', [status(thm)], ['189', '191'])).
% 5.22/5.46  thf('193', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.22/5.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.46  thf('194', plain, (((sk_B) = (k1_xboole_0))),
% 5.22/5.46      inference('clc', [status(thm)], ['164', '165'])).
% 5.22/5.46  thf('195', plain, ((v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 5.22/5.46      inference('demod', [status(thm)], ['193', '194'])).
% 5.22/5.46  thf('196', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 5.22/5.46      inference('demod', [status(thm)], ['192', '195'])).
% 5.22/5.46  thf('197', plain,
% 5.22/5.46      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 5.22/5.46      inference('sup-', [status(thm)], ['29', '30'])).
% 5.22/5.46  thf('198', plain, (((sk_B) = (k1_xboole_0))),
% 5.22/5.46      inference('clc', [status(thm)], ['164', '165'])).
% 5.22/5.46  thf('199', plain,
% 5.22/5.46      (((k1_relset_1 @ sk_A @ k1_xboole_0 @ sk_C) = (k1_relat_1 @ sk_C))),
% 5.22/5.46      inference('demod', [status(thm)], ['197', '198'])).
% 5.22/5.46  thf('200', plain,
% 5.22/5.46      ((((k1_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0) = (k1_relat_1 @ sk_C))
% 5.22/5.46        | ((sk_A) = (k1_xboole_0)))),
% 5.22/5.46      inference('sup+', [status(thm)], ['196', '199'])).
% 5.22/5.46  thf('201', plain,
% 5.22/5.46      (![X0 : $i, X1 : $i]:
% 5.22/5.46         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.22/5.46      inference('demod', [status(thm)], ['9', '20'])).
% 5.22/5.46  thf('202', plain,
% 5.22/5.46      ((((k1_xboole_0) = (k1_relat_1 @ sk_C)) | ((sk_A) = (k1_xboole_0)))),
% 5.22/5.46      inference('demod', [status(thm)], ['200', '201'])).
% 5.22/5.46  thf('203', plain,
% 5.22/5.46      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.22/5.46      inference('demod', [status(thm)], ['96', '97'])).
% 5.22/5.46  thf('204', plain, (((sk_B) = (k1_xboole_0))),
% 5.22/5.46      inference('clc', [status(thm)], ['164', '165'])).
% 5.22/5.46  thf('205', plain,
% 5.22/5.46      ((~ (zip_tseitin_1 @ sk_C @ k1_xboole_0 @ sk_A)
% 5.22/5.46        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.22/5.46      inference('demod', [status(thm)], ['203', '204'])).
% 5.22/5.46  thf('206', plain,
% 5.22/5.46      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.22/5.46      inference('sup-', [status(thm)], ['90', '91'])).
% 5.22/5.46  thf('207', plain, (((sk_B) = (k1_xboole_0))),
% 5.22/5.46      inference('clc', [status(thm)], ['164', '165'])).
% 5.22/5.46  thf('208', plain, (((sk_B) = (k1_xboole_0))),
% 5.22/5.46      inference('clc', [status(thm)], ['164', '165'])).
% 5.22/5.46  thf('209', plain,
% 5.22/5.46      (((zip_tseitin_1 @ sk_C @ k1_xboole_0 @ sk_A)
% 5.22/5.46        | ~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A))),
% 5.22/5.46      inference('demod', [status(thm)], ['206', '207', '208'])).
% 5.22/5.46  thf('210', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 5.22/5.46      inference('demod', [status(thm)], ['170', '173', '174', '175', '176'])).
% 5.22/5.46  thf('211', plain, ((zip_tseitin_1 @ sk_C @ k1_xboole_0 @ sk_A)),
% 5.22/5.46      inference('demod', [status(thm)], ['209', '210'])).
% 5.22/5.46  thf('212', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 5.22/5.46      inference('demod', [status(thm)], ['205', '211'])).
% 5.22/5.46  thf('213', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 5.22/5.46      inference('sup+', [status(thm)], ['202', '212'])).
% 5.22/5.46  thf('214', plain, (((sk_A) = (k1_xboole_0))),
% 5.22/5.46      inference('simplify', [status(thm)], ['213'])).
% 5.22/5.46  thf('215', plain,
% 5.22/5.46      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 5.22/5.46      inference('demod', [status(thm)], ['186', '214'])).
% 5.22/5.46  thf('216', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.22/5.46      inference('simplify', [status(thm)], ['48'])).
% 5.22/5.46  thf('217', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.22/5.46      inference('sup+', [status(thm)], ['41', '42'])).
% 5.22/5.46  thf('218', plain,
% 5.22/5.46      (![X35 : $i, X36 : $i]:
% 5.22/5.46         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 5.22/5.46          | (m1_subset_1 @ X35 @ 
% 5.22/5.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ X36)))
% 5.22/5.46          | ~ (v1_funct_1 @ X35)
% 5.22/5.46          | ~ (v1_relat_1 @ X35))),
% 5.22/5.46      inference('cnf', [status(esa)], [t4_funct_2])).
% 5.22/5.46  thf('219', plain,
% 5.22/5.46      (![X0 : $i]:
% 5.22/5.46         (~ (r1_tarski @ sk_B @ X0)
% 5.22/5.46          | ~ (v1_relat_1 @ sk_C)
% 5.22/5.46          | ~ (v1_funct_1 @ sk_C)
% 5.22/5.46          | (m1_subset_1 @ sk_C @ 
% 5.22/5.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ X0))))),
% 5.22/5.46      inference('sup-', [status(thm)], ['217', '218'])).
% 5.22/5.46  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.46      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.46  thf('221', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.46  thf('222', plain,
% 5.22/5.46      (![X0 : $i]:
% 5.22/5.46         (~ (r1_tarski @ sk_B @ X0)
% 5.22/5.46          | (m1_subset_1 @ sk_C @ 
% 5.22/5.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ X0))))),
% 5.22/5.46      inference('demod', [status(thm)], ['219', '220', '221'])).
% 5.22/5.46  thf('223', plain,
% 5.22/5.46      ((m1_subset_1 @ sk_C @ 
% 5.22/5.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 5.22/5.46      inference('sup-', [status(thm)], ['216', '222'])).
% 5.22/5.46  thf('224', plain, (((sk_B) = (k1_xboole_0))),
% 5.22/5.46      inference('clc', [status(thm)], ['164', '165'])).
% 5.22/5.46  thf('225', plain,
% 5.22/5.46      ((m1_subset_1 @ sk_C @ 
% 5.22/5.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))),
% 5.22/5.46      inference('demod', [status(thm)], ['223', '224'])).
% 5.22/5.46  thf('226', plain,
% 5.22/5.46      (![X33 : $i, X34 : $i]:
% 5.22/5.46         (~ (m1_subset_1 @ X34 @ 
% 5.22/5.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ k1_xboole_0)))
% 5.22/5.46          | ~ (v1_funct_2 @ X34 @ X33 @ k1_xboole_0)
% 5.22/5.46          | ((X34) = (k1_xboole_0))
% 5.22/5.46          | ((X33) = (k1_xboole_0)))),
% 5.22/5.46      inference('simplify', [status(thm)], ['190'])).
% 5.22/5.46  thf('227', plain,
% 5.22/5.46      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 5.22/5.46        | ((sk_C) = (k1_xboole_0))
% 5.22/5.46        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ k1_xboole_0))),
% 5.22/5.46      inference('sup-', [status(thm)], ['225', '226'])).
% 5.22/5.46  thf('228', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.22/5.46      inference('sup+', [status(thm)], ['41', '42'])).
% 5.22/5.46  thf('229', plain,
% 5.22/5.46      (![X35 : $i, X36 : $i]:
% 5.22/5.46         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 5.22/5.46          | (v1_funct_2 @ X35 @ (k1_relat_1 @ X35) @ X36)
% 5.22/5.46          | ~ (v1_funct_1 @ X35)
% 5.22/5.46          | ~ (v1_relat_1 @ X35))),
% 5.22/5.46      inference('cnf', [status(esa)], [t4_funct_2])).
% 5.22/5.46  thf('230', plain,
% 5.22/5.46      (![X0 : $i]:
% 5.22/5.46         (~ (r1_tarski @ sk_B @ X0)
% 5.22/5.46          | ~ (v1_relat_1 @ sk_C)
% 5.22/5.46          | ~ (v1_funct_1 @ sk_C)
% 5.22/5.46          | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ X0))),
% 5.22/5.46      inference('sup-', [status(thm)], ['228', '229'])).
% 5.22/5.46  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.46      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.46  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.46  thf('233', plain,
% 5.22/5.46      (![X0 : $i]:
% 5.22/5.46         (~ (r1_tarski @ sk_B @ X0)
% 5.22/5.46          | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ X0))),
% 5.22/5.46      inference('demod', [status(thm)], ['230', '231', '232'])).
% 5.22/5.46  thf('234', plain, (((sk_B) = (k1_xboole_0))),
% 5.22/5.46      inference('clc', [status(thm)], ['164', '165'])).
% 5.22/5.46  thf('235', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.22/5.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.22/5.46  thf('236', plain,
% 5.22/5.46      (![X0 : $i]: (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ X0)),
% 5.22/5.46      inference('demod', [status(thm)], ['233', '234', '235'])).
% 5.22/5.46  thf('237', plain,
% 5.22/5.46      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 5.22/5.46      inference('demod', [status(thm)], ['227', '236'])).
% 5.22/5.46  thf('238', plain,
% 5.22/5.46      (![X0 : $i]:
% 5.22/5.46         (~ (v2_funct_1 @ X0)
% 5.22/5.46          | ~ (v1_funct_1 @ X0)
% 5.22/5.46          | ~ (v1_relat_1 @ X0)
% 5.22/5.46          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.22/5.46             (k1_zfmisc_1 @ 
% 5.22/5.46              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 5.22/5.46      inference('simplify', [status(thm)], ['57'])).
% 5.22/5.46  thf('239', plain,
% 5.22/5.46      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ k1_xboole_0)))
% 5.22/5.46        | ((sk_C) = (k1_xboole_0))
% 5.22/5.46        | ~ (v1_relat_1 @ sk_C)
% 5.22/5.46        | ~ (v1_funct_1 @ sk_C)
% 5.22/5.46        | ~ (v2_funct_1 @ sk_C))),
% 5.22/5.46      inference('sup+', [status(thm)], ['237', '238'])).
% 5.22/5.46  thf('240', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 5.22/5.46      inference('demod', [status(thm)], ['171', '172'])).
% 5.22/5.46  thf('241', plain, ((v1_relat_1 @ sk_C)),
% 5.22/5.46      inference('sup-', [status(thm)], ['60', '61'])).
% 5.22/5.46  thf('242', plain, ((v1_funct_1 @ sk_C)),
% 5.22/5.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.46  thf('243', plain, ((v2_funct_1 @ sk_C)),
% 5.22/5.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.22/5.46  thf('244', plain,
% 5.22/5.46      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 5.22/5.46        | ((sk_C) = (k1_xboole_0)))),
% 5.22/5.46      inference('demod', [status(thm)], ['239', '240', '241', '242', '243'])).
% 5.22/5.46  thf('245', plain,
% 5.22/5.46      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.22/5.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 5.22/5.46      inference('demod', [status(thm)], ['186', '214'])).
% 5.22/5.46  thf('246', plain, (((sk_C) = (k1_xboole_0))),
% 5.22/5.46      inference('sup-', [status(thm)], ['244', '245'])).
% 5.22/5.46  thf('247', plain,
% 5.22/5.46      (~ (m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 5.22/5.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 5.22/5.46      inference('demod', [status(thm)], ['215', '246'])).
% 5.22/5.46  thf('248', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 5.22/5.46      inference('demod', [status(thm)], ['23', '181'])).
% 5.22/5.46  thf('249', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 5.22/5.46      inference('demod', [status(thm)], ['23', '181'])).
% 5.22/5.46  thf('250', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 5.22/5.46      inference('demod', [status(thm)], ['23', '181'])).
% 5.22/5.46  thf('251', plain, (~ (m1_subset_1 @ k1_xboole_0 @ k1_xboole_0)),
% 5.22/5.46      inference('demod', [status(thm)], ['247', '248', '249', '250'])).
% 5.22/5.46  thf('252', plain, (![X0 : $i]: ~ (m1_subset_1 @ X0 @ k1_xboole_0)),
% 5.22/5.46      inference('sup-', [status(thm)], ['185', '251'])).
% 5.22/5.46  thf('253', plain, (![X0 : $i, X1 : $i]: ~ (m1_subset_1 @ X1 @ X0)),
% 5.22/5.46      inference('sup-', [status(thm)], ['184', '252'])).
% 5.22/5.46  thf('254', plain, ($false), inference('sup-', [status(thm)], ['183', '253'])).
% 5.22/5.46  
% 5.22/5.46  % SZS output end Refutation
% 5.22/5.46  
% 5.22/5.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
