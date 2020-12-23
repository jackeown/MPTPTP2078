%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L2Jkw1A4wr

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:44 EST 2020

% Result     : Theorem 2.78s
% Output     : Refutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 500 expanded)
%              Number of leaves         :   38 ( 159 expanded)
%              Depth                    :   20
%              Number of atoms          : 1376 (7422 expanded)
%              Number of equality atoms :   68 ( 314 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(zf_stmt_0,negated_conjecture,(
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

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ( X3
       != ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('36',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('42',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('44',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

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

thf('50',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['33','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['32','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('65',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('69',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('70',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('71',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['67','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('82',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('83',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','85'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','86','87'])).

thf('89',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','88'])).

thf('90',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('92',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('93',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('94',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('95',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['91','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('103',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['90','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('108',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('113',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('115',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','86','87'])).

thf('117',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('119',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','117','118','119','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['89','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L2Jkw1A4wr
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:28:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.78/2.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.78/2.99  % Solved by: fo/fo7.sh
% 2.78/2.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.78/2.99  % done 2909 iterations in 2.541s
% 2.78/2.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.78/2.99  % SZS output start Refutation
% 2.78/2.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.78/2.99  thf(sk_A_type, type, sk_A: $i).
% 2.78/2.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.78/2.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.78/2.99  thf(sk_B_type, type, sk_B: $i).
% 2.78/2.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.78/2.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.78/2.99  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.78/2.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.78/2.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.78/2.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.78/2.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.78/2.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.78/2.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.78/2.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.78/2.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.78/2.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.78/2.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.78/2.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.78/2.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.78/2.99  thf(t31_funct_2, conjecture,
% 2.78/2.99    (![A:$i,B:$i,C:$i]:
% 2.78/2.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.78/2.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.78/2.99       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.78/2.99         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.78/2.99           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.78/2.99           ( m1_subset_1 @
% 2.78/2.99             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.78/2.99  thf(zf_stmt_0, negated_conjecture,
% 2.78/2.99    (~( ![A:$i,B:$i,C:$i]:
% 2.78/2.99        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.78/2.99            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.78/2.99          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.78/2.99            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.78/2.99              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.78/2.99              ( m1_subset_1 @
% 2.78/2.99                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 2.78/2.99    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 2.78/2.99  thf('0', plain,
% 2.78/2.99      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 2.78/2.99        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 2.78/2.99        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('1', plain,
% 2.78/2.99      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.78/2.99         <= (~
% 2.78/2.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.78/2.99      inference('split', [status(esa)], ['0'])).
% 2.78/2.99  thf('2', plain,
% 2.78/2.99      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf(cc1_relset_1, axiom,
% 2.78/2.99    (![A:$i,B:$i,C:$i]:
% 2.78/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.78/2.99       ( v1_relat_1 @ C ) ))).
% 2.78/2.99  thf('3', plain,
% 2.78/2.99      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.78/2.99         ((v1_relat_1 @ X15)
% 2.78/2.99          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.78/2.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.78/2.99  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 2.78/2.99      inference('sup-', [status(thm)], ['2', '3'])).
% 2.78/2.99  thf(dt_k2_funct_1, axiom,
% 2.78/2.99    (![A:$i]:
% 2.78/2.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.78/2.99       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.78/2.99         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.78/2.99  thf('5', plain,
% 2.78/2.99      (![X12 : $i]:
% 2.78/2.99         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 2.78/2.99          | ~ (v1_funct_1 @ X12)
% 2.78/2.99          | ~ (v1_relat_1 @ X12))),
% 2.78/2.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.78/2.99  thf('6', plain,
% 2.78/2.99      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 2.78/2.99         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 2.78/2.99      inference('split', [status(esa)], ['0'])).
% 2.78/2.99  thf('7', plain,
% 2.78/2.99      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 2.78/2.99         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 2.78/2.99      inference('sup-', [status(thm)], ['5', '6'])).
% 2.78/2.99  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('9', plain,
% 2.78/2.99      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 2.78/2.99      inference('demod', [status(thm)], ['7', '8'])).
% 2.78/2.99  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 2.78/2.99      inference('sup-', [status(thm)], ['4', '9'])).
% 2.78/2.99  thf('11', plain,
% 2.78/2.99      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 2.78/2.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.78/2.99      inference('split', [status(esa)], ['0'])).
% 2.78/2.99  thf('12', plain,
% 2.78/2.99      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf(redefinition_k2_relset_1, axiom,
% 2.78/2.99    (![A:$i,B:$i,C:$i]:
% 2.78/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.78/2.99       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.78/2.99  thf('13', plain,
% 2.78/2.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.78/2.99         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 2.78/2.99          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.78/2.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.78/2.99  thf('14', plain,
% 2.78/2.99      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 2.78/2.99      inference('sup-', [status(thm)], ['12', '13'])).
% 2.78/2.99  thf('15', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('16', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 2.78/2.99      inference('sup+', [status(thm)], ['14', '15'])).
% 2.78/2.99  thf(d1_funct_2, axiom,
% 2.78/2.99    (![A:$i,B:$i,C:$i]:
% 2.78/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.78/2.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.78/2.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.78/2.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.78/2.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.78/2.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.78/2.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.78/2.99  thf(zf_stmt_1, axiom,
% 2.78/2.99    (![B:$i,A:$i]:
% 2.78/2.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.78/2.99       ( zip_tseitin_0 @ B @ A ) ))).
% 2.78/2.99  thf('17', plain,
% 2.78/2.99      (![X24 : $i, X25 : $i]:
% 2.78/2.99         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.78/2.99  thf('18', plain,
% 2.78/2.99      (![X12 : $i]:
% 2.78/2.99         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 2.78/2.99          | ~ (v1_funct_1 @ X12)
% 2.78/2.99          | ~ (v1_relat_1 @ X12))),
% 2.78/2.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.78/2.99  thf(t55_funct_1, axiom,
% 2.78/2.99    (![A:$i]:
% 2.78/2.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.78/2.99       ( ( v2_funct_1 @ A ) =>
% 2.78/2.99         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.78/2.99           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.78/2.99  thf('19', plain,
% 2.78/2.99      (![X13 : $i]:
% 2.78/2.99         (~ (v2_funct_1 @ X13)
% 2.78/2.99          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 2.78/2.99          | ~ (v1_funct_1 @ X13)
% 2.78/2.99          | ~ (v1_relat_1 @ X13))),
% 2.78/2.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.78/2.99  thf(t64_relat_1, axiom,
% 2.78/2.99    (![A:$i]:
% 2.78/2.99     ( ( v1_relat_1 @ A ) =>
% 2.78/2.99       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 2.78/2.99           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.78/2.99         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 2.78/2.99  thf('20', plain,
% 2.78/2.99      (![X11 : $i]:
% 2.78/2.99         (((k1_relat_1 @ X11) != (k1_xboole_0))
% 2.78/2.99          | ((X11) = (k1_xboole_0))
% 2.78/2.99          | ~ (v1_relat_1 @ X11))),
% 2.78/2.99      inference('cnf', [status(esa)], [t64_relat_1])).
% 2.78/2.99  thf('21', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 2.78/2.99          | ~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.78/2.99          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 2.78/2.99      inference('sup-', [status(thm)], ['19', '20'])).
% 2.78/2.99  thf('22', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         (~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0)
% 2.78/2.99          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 2.78/2.99      inference('sup-', [status(thm)], ['18', '21'])).
% 2.78/2.99  thf('23', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0))),
% 2.78/2.99      inference('simplify', [status(thm)], ['22'])).
% 2.78/2.99  thf('24', plain,
% 2.78/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.99         (((k2_relat_1 @ X1) != (X0))
% 2.78/2.99          | (zip_tseitin_0 @ X0 @ X2)
% 2.78/2.99          | ~ (v1_relat_1 @ X1)
% 2.78/2.99          | ~ (v1_funct_1 @ X1)
% 2.78/2.99          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 2.78/2.99          | ~ (v2_funct_1 @ X1))),
% 2.78/2.99      inference('sup-', [status(thm)], ['17', '23'])).
% 2.78/2.99  thf('25', plain,
% 2.78/2.99      (![X1 : $i, X2 : $i]:
% 2.78/2.99         (~ (v2_funct_1 @ X1)
% 2.78/2.99          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 2.78/2.99          | ~ (v1_funct_1 @ X1)
% 2.78/2.99          | ~ (v1_relat_1 @ X1)
% 2.78/2.99          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 2.78/2.99      inference('simplify', [status(thm)], ['24'])).
% 2.78/2.99  thf('26', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         ((zip_tseitin_0 @ sk_B @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ sk_C_1)
% 2.78/2.99          | ~ (v1_funct_1 @ sk_C_1)
% 2.78/2.99          | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0))
% 2.78/2.99          | ~ (v2_funct_1 @ sk_C_1))),
% 2.78/2.99      inference('sup+', [status(thm)], ['16', '25'])).
% 2.78/2.99  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 2.78/2.99      inference('sup-', [status(thm)], ['2', '3'])).
% 2.78/2.99  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('29', plain, ((v2_funct_1 @ sk_C_1)),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('30', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0)))),
% 2.78/2.99      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.78/2.99  thf('31', plain,
% 2.78/2.99      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 2.78/2.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.78/2.99      inference('split', [status(esa)], ['0'])).
% 2.78/2.99  thf('32', plain,
% 2.78/2.99      ((![X0 : $i]:
% 2.78/2.99          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 2.78/2.99           | (zip_tseitin_0 @ sk_B @ X0)))
% 2.78/2.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.78/2.99      inference('sup-', [status(thm)], ['30', '31'])).
% 2.78/2.99  thf('33', plain,
% 2.78/2.99      (![X24 : $i, X25 : $i]:
% 2.78/2.99         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.78/2.99  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.78/2.99  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.78/2.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.78/2.99  thf(d1_zfmisc_1, axiom,
% 2.78/2.99    (![A:$i,B:$i]:
% 2.78/2.99     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.78/2.99       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.78/2.99  thf('35', plain,
% 2.78/2.99      (![X1 : $i, X2 : $i, X3 : $i]:
% 2.78/2.99         (~ (r1_tarski @ X1 @ X2)
% 2.78/2.99          | (r2_hidden @ X1 @ X3)
% 2.78/2.99          | ((X3) != (k1_zfmisc_1 @ X2)))),
% 2.78/2.99      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.78/2.99  thf('36', plain,
% 2.78/2.99      (![X1 : $i, X2 : $i]:
% 2.78/2.99         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X1 @ X2))),
% 2.78/2.99      inference('simplify', [status(thm)], ['35'])).
% 2.78/2.99  thf('37', plain,
% 2.78/2.99      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.78/2.99      inference('sup-', [status(thm)], ['34', '36'])).
% 2.78/2.99  thf(t1_subset, axiom,
% 2.78/2.99    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 2.78/2.99  thf('38', plain,
% 2.78/2.99      (![X9 : $i, X10 : $i]:
% 2.78/2.99         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 2.78/2.99      inference('cnf', [status(esa)], [t1_subset])).
% 2.78/2.99  thf('39', plain,
% 2.78/2.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.78/2.99      inference('sup-', [status(thm)], ['37', '38'])).
% 2.78/2.99  thf(redefinition_k1_relset_1, axiom,
% 2.78/2.99    (![A:$i,B:$i,C:$i]:
% 2.78/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.78/2.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.78/2.99  thf('40', plain,
% 2.78/2.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.78/2.99         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 2.78/2.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.78/2.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.78/2.99  thf('41', plain,
% 2.78/2.99      (![X0 : $i, X1 : $i]:
% 2.78/2.99         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.78/2.99      inference('sup-', [status(thm)], ['39', '40'])).
% 2.78/2.99  thf(t60_relat_1, axiom,
% 2.78/2.99    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.78/2.99     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.78/2.99  thf('42', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.78/2.99      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.78/2.99  thf('43', plain,
% 2.78/2.99      (![X0 : $i, X1 : $i]:
% 2.78/2.99         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.78/2.99      inference('demod', [status(thm)], ['41', '42'])).
% 2.78/2.99  thf(zf_stmt_2, axiom,
% 2.78/2.99    (![C:$i,B:$i,A:$i]:
% 2.78/2.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.78/2.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.78/2.99  thf('44', plain,
% 2.78/2.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.78/2.99         (((X26) != (k1_relset_1 @ X26 @ X27 @ X28))
% 2.78/2.99          | (v1_funct_2 @ X28 @ X26 @ X27)
% 2.78/2.99          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.78/2.99  thf('45', plain,
% 2.78/2.99      (![X0 : $i, X1 : $i]:
% 2.78/2.99         (((X1) != (k1_xboole_0))
% 2.78/2.99          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 2.78/2.99          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 2.78/2.99      inference('sup-', [status(thm)], ['43', '44'])).
% 2.78/2.99  thf('46', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 2.78/2.99          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 2.78/2.99      inference('simplify', [status(thm)], ['45'])).
% 2.78/2.99  thf('47', plain,
% 2.78/2.99      (![X24 : $i, X25 : $i]:
% 2.78/2.99         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.78/2.99  thf('48', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 2.78/2.99      inference('simplify', [status(thm)], ['47'])).
% 2.78/2.99  thf('49', plain,
% 2.78/2.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.78/2.99      inference('sup-', [status(thm)], ['37', '38'])).
% 2.78/2.99  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.78/2.99  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.78/2.99  thf(zf_stmt_5, axiom,
% 2.78/2.99    (![A:$i,B:$i,C:$i]:
% 2.78/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.78/2.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.78/2.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.78/2.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.78/2.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.78/2.99  thf('50', plain,
% 2.78/2.99      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.78/2.99         (~ (zip_tseitin_0 @ X29 @ X30)
% 2.78/2.99          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 2.78/2.99          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.78/2.99  thf('51', plain,
% 2.78/2.99      (![X0 : $i, X1 : $i]:
% 2.78/2.99         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 2.78/2.99      inference('sup-', [status(thm)], ['49', '50'])).
% 2.78/2.99  thf('52', plain,
% 2.78/2.99      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.78/2.99      inference('sup-', [status(thm)], ['48', '51'])).
% 2.78/2.99  thf('53', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.78/2.99      inference('demod', [status(thm)], ['46', '52'])).
% 2.78/2.99  thf('54', plain,
% 2.78/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.99         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 2.78/2.99      inference('sup+', [status(thm)], ['33', '53'])).
% 2.78/2.99  thf('55', plain,
% 2.78/2.99      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 2.78/2.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.78/2.99      inference('clc', [status(thm)], ['32', '54'])).
% 2.78/2.99  thf('56', plain,
% 2.78/2.99      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('57', plain,
% 2.78/2.99      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.78/2.99         (~ (zip_tseitin_0 @ X29 @ X30)
% 2.78/2.99          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 2.78/2.99          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.78/2.99  thf('58', plain,
% 2.78/2.99      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.78/2.99        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.78/2.99      inference('sup-', [status(thm)], ['56', '57'])).
% 2.78/2.99  thf('59', plain,
% 2.78/2.99      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))
% 2.78/2.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.78/2.99      inference('sup-', [status(thm)], ['55', '58'])).
% 2.78/2.99  thf('60', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('61', plain,
% 2.78/2.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.78/2.99         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 2.78/2.99          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 2.78/2.99          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.78/2.99  thf('62', plain,
% 2.78/2.99      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.78/2.99        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.78/2.99      inference('sup-', [status(thm)], ['60', '61'])).
% 2.78/2.99  thf('63', plain,
% 2.78/2.99      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('64', plain,
% 2.78/2.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.78/2.99         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 2.78/2.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.78/2.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.78/2.99  thf('65', plain,
% 2.78/2.99      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 2.78/2.99      inference('sup-', [status(thm)], ['63', '64'])).
% 2.78/2.99  thf('66', plain,
% 2.78/2.99      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.78/2.99        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 2.78/2.99      inference('demod', [status(thm)], ['62', '65'])).
% 2.78/2.99  thf('67', plain,
% 2.78/2.99      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 2.78/2.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.78/2.99      inference('sup-', [status(thm)], ['59', '66'])).
% 2.78/2.99  thf('68', plain,
% 2.78/2.99      (![X13 : $i]:
% 2.78/2.99         (~ (v2_funct_1 @ X13)
% 2.78/2.99          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 2.78/2.99          | ~ (v1_funct_1 @ X13)
% 2.78/2.99          | ~ (v1_relat_1 @ X13))),
% 2.78/2.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.78/2.99  thf('69', plain,
% 2.78/2.99      (![X12 : $i]:
% 2.78/2.99         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 2.78/2.99          | ~ (v1_funct_1 @ X12)
% 2.78/2.99          | ~ (v1_relat_1 @ X12))),
% 2.78/2.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.78/2.99  thf('70', plain,
% 2.78/2.99      (![X12 : $i]:
% 2.78/2.99         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 2.78/2.99          | ~ (v1_funct_1 @ X12)
% 2.78/2.99          | ~ (v1_relat_1 @ X12))),
% 2.78/2.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.78/2.99  thf('71', plain,
% 2.78/2.99      (![X13 : $i]:
% 2.78/2.99         (~ (v2_funct_1 @ X13)
% 2.78/2.99          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 2.78/2.99          | ~ (v1_funct_1 @ X13)
% 2.78/2.99          | ~ (v1_relat_1 @ X13))),
% 2.78/2.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.78/2.99  thf(t3_funct_2, axiom,
% 2.78/2.99    (![A:$i]:
% 2.78/2.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.78/2.99       ( ( v1_funct_1 @ A ) & 
% 2.78/2.99         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.78/2.99         ( m1_subset_1 @
% 2.78/2.99           A @ 
% 2.78/2.99           ( k1_zfmisc_1 @
% 2.78/2.99             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.78/2.99  thf('72', plain,
% 2.78/2.99      (![X32 : $i]:
% 2.78/2.99         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 2.78/2.99          | ~ (v1_funct_1 @ X32)
% 2.78/2.99          | ~ (v1_relat_1 @ X32))),
% 2.78/2.99      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.78/2.99  thf('73', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.78/2.99           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.78/2.99          | ~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.78/2.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.78/2.99      inference('sup+', [status(thm)], ['71', '72'])).
% 2.78/2.99  thf('74', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         (~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0)
% 2.78/2.99          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.78/2.99             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.78/2.99      inference('sup-', [status(thm)], ['70', '73'])).
% 2.78/2.99  thf('75', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.78/2.99           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0))),
% 2.78/2.99      inference('simplify', [status(thm)], ['74'])).
% 2.78/2.99  thf('76', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         (~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.78/2.99             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.78/2.99      inference('sup-', [status(thm)], ['69', '75'])).
% 2.78/2.99  thf('77', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.78/2.99           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0))),
% 2.78/2.99      inference('simplify', [status(thm)], ['76'])).
% 2.78/2.99  thf('78', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.78/2.99           (k1_relat_1 @ X0))
% 2.78/2.99          | ~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v2_funct_1 @ X0))),
% 2.78/2.99      inference('sup+', [status(thm)], ['68', '77'])).
% 2.78/2.99  thf('79', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         (~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0)
% 2.78/2.99          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.78/2.99             (k1_relat_1 @ X0)))),
% 2.78/2.99      inference('simplify', [status(thm)], ['78'])).
% 2.78/2.99  thf('80', plain,
% 2.78/2.99      ((((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_A)
% 2.78/2.99         | ~ (v1_relat_1 @ sk_C_1)
% 2.78/2.99         | ~ (v1_funct_1 @ sk_C_1)
% 2.78/2.99         | ~ (v2_funct_1 @ sk_C_1)))
% 2.78/2.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.78/2.99      inference('sup+', [status(thm)], ['67', '79'])).
% 2.78/2.99  thf('81', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 2.78/2.99      inference('sup+', [status(thm)], ['14', '15'])).
% 2.78/2.99  thf('82', plain, ((v1_relat_1 @ sk_C_1)),
% 2.78/2.99      inference('sup-', [status(thm)], ['2', '3'])).
% 2.78/2.99  thf('83', plain, ((v1_funct_1 @ sk_C_1)),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('84', plain, ((v2_funct_1 @ sk_C_1)),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('85', plain,
% 2.78/2.99      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 2.78/2.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.78/2.99      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 2.78/2.99  thf('86', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 2.78/2.99      inference('demod', [status(thm)], ['11', '85'])).
% 2.78/2.99  thf('87', plain,
% 2.78/2.99      (~
% 2.78/2.99       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 2.78/2.99       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 2.78/2.99       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 2.78/2.99      inference('split', [status(esa)], ['0'])).
% 2.78/2.99  thf('88', plain,
% 2.78/2.99      (~
% 2.78/2.99       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.78/2.99      inference('sat_resolution*', [status(thm)], ['10', '86', '87'])).
% 2.78/2.99  thf('89', plain,
% 2.78/2.99      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.78/2.99      inference('simpl_trail', [status(thm)], ['1', '88'])).
% 2.78/2.99  thf('90', plain,
% 2.78/2.99      (![X13 : $i]:
% 2.78/2.99         (~ (v2_funct_1 @ X13)
% 2.78/2.99          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 2.78/2.99          | ~ (v1_funct_1 @ X13)
% 2.78/2.99          | ~ (v1_relat_1 @ X13))),
% 2.78/2.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.78/2.99  thf('91', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 2.78/2.99      inference('sup+', [status(thm)], ['14', '15'])).
% 2.78/2.99  thf('92', plain,
% 2.78/2.99      (![X12 : $i]:
% 2.78/2.99         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 2.78/2.99          | ~ (v1_funct_1 @ X12)
% 2.78/2.99          | ~ (v1_relat_1 @ X12))),
% 2.78/2.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.78/2.99  thf('93', plain,
% 2.78/2.99      (![X12 : $i]:
% 2.78/2.99         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 2.78/2.99          | ~ (v1_funct_1 @ X12)
% 2.78/2.99          | ~ (v1_relat_1 @ X12))),
% 2.78/2.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.78/2.99  thf('94', plain,
% 2.78/2.99      (![X13 : $i]:
% 2.78/2.99         (~ (v2_funct_1 @ X13)
% 2.78/2.99          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 2.78/2.99          | ~ (v1_funct_1 @ X13)
% 2.78/2.99          | ~ (v1_relat_1 @ X13))),
% 2.78/2.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.78/2.99  thf('95', plain,
% 2.78/2.99      (![X32 : $i]:
% 2.78/2.99         ((m1_subset_1 @ X32 @ 
% 2.78/2.99           (k1_zfmisc_1 @ 
% 2.78/2.99            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 2.78/2.99          | ~ (v1_funct_1 @ X32)
% 2.78/2.99          | ~ (v1_relat_1 @ X32))),
% 2.78/2.99      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.78/2.99  thf('96', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.78/2.99           (k1_zfmisc_1 @ 
% 2.78/2.99            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.78/2.99          | ~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.78/2.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.78/2.99      inference('sup+', [status(thm)], ['94', '95'])).
% 2.78/2.99  thf('97', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         (~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0)
% 2.78/2.99          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.78/2.99             (k1_zfmisc_1 @ 
% 2.78/2.99              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.78/2.99               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.78/2.99      inference('sup-', [status(thm)], ['93', '96'])).
% 2.78/2.99  thf('98', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.78/2.99           (k1_zfmisc_1 @ 
% 2.78/2.99            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0))),
% 2.78/2.99      inference('simplify', [status(thm)], ['97'])).
% 2.78/2.99  thf('99', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         (~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.78/2.99             (k1_zfmisc_1 @ 
% 2.78/2.99              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.78/2.99               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.78/2.99      inference('sup-', [status(thm)], ['92', '98'])).
% 2.78/2.99  thf('100', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.78/2.99           (k1_zfmisc_1 @ 
% 2.78/2.99            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.78/2.99          | ~ (v2_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_funct_1 @ X0)
% 2.78/2.99          | ~ (v1_relat_1 @ X0))),
% 2.78/2.99      inference('simplify', [status(thm)], ['99'])).
% 2.78/2.99  thf('101', plain,
% 2.78/2.99      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99         (k1_zfmisc_1 @ 
% 2.78/2.99          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))
% 2.78/2.99        | ~ (v1_relat_1 @ sk_C_1)
% 2.78/2.99        | ~ (v1_funct_1 @ sk_C_1)
% 2.78/2.99        | ~ (v2_funct_1 @ sk_C_1))),
% 2.78/2.99      inference('sup+', [status(thm)], ['91', '100'])).
% 2.78/2.99  thf('102', plain, ((v1_relat_1 @ sk_C_1)),
% 2.78/2.99      inference('sup-', [status(thm)], ['2', '3'])).
% 2.78/2.99  thf('103', plain, ((v1_funct_1 @ sk_C_1)),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('104', plain, ((v2_funct_1 @ sk_C_1)),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('105', plain,
% 2.78/2.99      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99        (k1_zfmisc_1 @ 
% 2.78/2.99         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 2.78/2.99      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 2.78/2.99  thf('106', plain,
% 2.78/2.99      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))
% 2.78/2.99        | ~ (v1_relat_1 @ sk_C_1)
% 2.78/2.99        | ~ (v1_funct_1 @ sk_C_1)
% 2.78/2.99        | ~ (v2_funct_1 @ sk_C_1))),
% 2.78/2.99      inference('sup+', [status(thm)], ['90', '105'])).
% 2.78/2.99  thf('107', plain,
% 2.78/2.99      (![X0 : $i]:
% 2.78/2.99         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0)))),
% 2.78/2.99      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.78/2.99  thf('108', plain,
% 2.78/2.99      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.78/2.99         <= (~
% 2.78/2.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.78/2.99      inference('split', [status(esa)], ['0'])).
% 2.78/2.99  thf('109', plain,
% 2.78/2.99      ((![X0 : $i]:
% 2.78/2.99          (~ (m1_subset_1 @ k1_xboole_0 @ 
% 2.78/2.99              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.78/2.99           | (zip_tseitin_0 @ sk_B @ X0)))
% 2.78/2.99         <= (~
% 2.78/2.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.78/2.99      inference('sup-', [status(thm)], ['107', '108'])).
% 2.78/2.99  thf('110', plain,
% 2.78/2.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.78/2.99      inference('sup-', [status(thm)], ['37', '38'])).
% 2.78/2.99  thf('111', plain,
% 2.78/2.99      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 2.78/2.99         <= (~
% 2.78/2.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.78/2.99      inference('demod', [status(thm)], ['109', '110'])).
% 2.78/2.99  thf('112', plain,
% 2.78/2.99      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.78/2.99        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.78/2.99      inference('sup-', [status(thm)], ['56', '57'])).
% 2.78/2.99  thf('113', plain,
% 2.78/2.99      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))
% 2.78/2.99         <= (~
% 2.78/2.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.78/2.99      inference('sup-', [status(thm)], ['111', '112'])).
% 2.78/2.99  thf('114', plain,
% 2.78/2.99      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.78/2.99        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 2.78/2.99      inference('demod', [status(thm)], ['62', '65'])).
% 2.78/2.99  thf('115', plain,
% 2.78/2.99      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 2.78/2.99         <= (~
% 2.78/2.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.78/2.99      inference('sup-', [status(thm)], ['113', '114'])).
% 2.78/2.99  thf('116', plain,
% 2.78/2.99      (~
% 2.78/2.99       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.78/2.99      inference('sat_resolution*', [status(thm)], ['10', '86', '87'])).
% 2.78/2.99  thf('117', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 2.78/2.99      inference('simpl_trail', [status(thm)], ['115', '116'])).
% 2.78/2.99  thf('118', plain, ((v1_relat_1 @ sk_C_1)),
% 2.78/2.99      inference('sup-', [status(thm)], ['2', '3'])).
% 2.78/2.99  thf('119', plain, ((v1_funct_1 @ sk_C_1)),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('120', plain, ((v2_funct_1 @ sk_C_1)),
% 2.78/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.99  thf('121', plain,
% 2.78/2.99      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.78/2.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.78/2.99      inference('demod', [status(thm)], ['106', '117', '118', '119', '120'])).
% 2.78/2.99  thf('122', plain, ($false), inference('demod', [status(thm)], ['89', '121'])).
% 2.78/2.99  
% 2.78/2.99  % SZS output end Refutation
% 2.78/2.99  
% 2.78/3.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
