%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zsJJfTKP4O

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:06 EST 2020

% Result     : Theorem 3.49s
% Output     : Refutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 497 expanded)
%              Number of leaves         :   42 ( 167 expanded)
%              Depth                    :   15
%              Number of atoms          : 1355 (9801 expanded)
%              Number of equality atoms :  105 ( 225 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
       != k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('8',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X0 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('22',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','12'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('23',plain,(
    ! [X5: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X5 ) )
      = ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('24',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','12'])).

thf('26',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('28',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_funct_2 @ X27 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v3_funct_2 @ X19 @ X20 @ X21 )
      | ( v2_funct_2 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('41',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_2 @ X23 @ X22 )
      | ( ( k2_relat_1 @ X23 )
        = X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('55',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','12'])).

thf('56',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['38','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','52'])).

thf('64',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
       != k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('65',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('67',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('70',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33
        = ( k2_funct_1 @ X36 ) )
      | ~ ( r2_relset_1 @ X35 @ X35 @ ( k1_partfun1 @ X35 @ X34 @ X34 @ X35 @ X36 @ X33 ) @ ( k6_partfun1 @ X35 ) )
      | ( X34 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('73',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('74',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33
        = ( k2_funct_1 @ X36 ) )
      | ~ ( r2_relset_1 @ X35 @ X35 @ ( k1_partfun1 @ X35 @ X34 @ X34 @ X35 @ X36 @ X33 ) @ ( k6_relat_1 @ X35 ) )
      | ( X34 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('85',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('86',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','52'])).

thf('88',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v3_funct_2 @ X19 @ X20 @ X21 )
      | ( v2_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('91',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','88','94'])).

thf('96',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('98',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('101',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','102'])).

thf('104',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('106',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['62','104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v3_funct_2 @ X19 @ X20 @ X21 )
      | ( v2_funct_2 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('109',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_2 @ X23 @ X22 )
      | ( ( k2_relat_1 @ X23 )
        = X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('120',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['114','117','120'])).

thf('122',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
       != k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('123',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['115','116'])).

thf('125',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','101'])).

thf('127',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['106','128','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zsJJfTKP4O
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.49/3.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.49/3.74  % Solved by: fo/fo7.sh
% 3.49/3.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.49/3.74  % done 5349 iterations in 3.273s
% 3.49/3.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.49/3.74  % SZS output start Refutation
% 3.49/3.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.49/3.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.49/3.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.49/3.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.49/3.74  thf(sk_B_type, type, sk_B: $i).
% 3.49/3.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.49/3.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.49/3.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.49/3.74  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.49/3.74  thf(sk_C_type, type, sk_C: $i).
% 3.49/3.74  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 3.49/3.74  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.49/3.74  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.49/3.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.49/3.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.49/3.74  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.49/3.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.49/3.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.49/3.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.49/3.74  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.49/3.74  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 3.49/3.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.49/3.74  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.49/3.74  thf(sk_A_type, type, sk_A: $i).
% 3.49/3.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.49/3.74  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.49/3.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.49/3.74  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.49/3.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.49/3.74  thf(t8_boole, axiom,
% 3.49/3.74    (![A:$i,B:$i]:
% 3.49/3.74     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.49/3.74  thf('1', plain,
% 3.49/3.74      (![X0 : $i, X1 : $i]:
% 3.49/3.74         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.49/3.74      inference('cnf', [status(esa)], [t8_boole])).
% 3.49/3.74  thf('2', plain,
% 3.49/3.74      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.49/3.74      inference('sup-', [status(thm)], ['0', '1'])).
% 3.49/3.74  thf('3', plain,
% 3.49/3.74      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.49/3.74      inference('sup-', [status(thm)], ['0', '1'])).
% 3.49/3.74  thf(t71_relat_1, axiom,
% 3.49/3.74    (![A:$i]:
% 3.49/3.74     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.49/3.74       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.49/3.74  thf('4', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 3.49/3.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.49/3.74  thf(t64_relat_1, axiom,
% 3.49/3.74    (![A:$i]:
% 3.49/3.74     ( ( v1_relat_1 @ A ) =>
% 3.49/3.74       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 3.49/3.74           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.49/3.74         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 3.49/3.74  thf('5', plain,
% 3.49/3.74      (![X2 : $i]:
% 3.49/3.74         (((k2_relat_1 @ X2) != (k1_xboole_0))
% 3.49/3.74          | ((X2) = (k1_xboole_0))
% 3.49/3.74          | ~ (v1_relat_1 @ X2))),
% 3.49/3.74      inference('cnf', [status(esa)], [t64_relat_1])).
% 3.49/3.74  thf('6', plain,
% 3.49/3.74      (![X0 : $i]:
% 3.49/3.74         (((X0) != (k1_xboole_0))
% 3.49/3.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.49/3.74          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 3.49/3.74      inference('sup-', [status(thm)], ['4', '5'])).
% 3.49/3.74  thf('7', plain,
% 3.49/3.74      ((((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 3.49/3.74        | ~ (v1_relat_1 @ (k6_relat_1 @ k1_xboole_0)))),
% 3.49/3.74      inference('simplify', [status(thm)], ['6'])).
% 3.49/3.74  thf(dt_k6_partfun1, axiom,
% 3.49/3.74    (![A:$i]:
% 3.49/3.74     ( ( m1_subset_1 @
% 3.49/3.74         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.49/3.74       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.49/3.74  thf('8', plain,
% 3.49/3.74      (![X25 : $i]:
% 3.49/3.74         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 3.49/3.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 3.49/3.74      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.49/3.74  thf(redefinition_k6_partfun1, axiom,
% 3.49/3.74    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.49/3.74  thf('9', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 3.49/3.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.49/3.74  thf('10', plain,
% 3.49/3.74      (![X25 : $i]:
% 3.49/3.74         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 3.49/3.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 3.49/3.74      inference('demod', [status(thm)], ['8', '9'])).
% 3.49/3.74  thf(cc1_relset_1, axiom,
% 3.49/3.74    (![A:$i,B:$i,C:$i]:
% 3.49/3.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.49/3.74       ( v1_relat_1 @ C ) ))).
% 3.49/3.74  thf('11', plain,
% 3.49/3.74      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.49/3.74         ((v1_relat_1 @ X6)
% 3.49/3.74          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 3.49/3.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.49/3.74  thf('12', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 3.49/3.74      inference('sup-', [status(thm)], ['10', '11'])).
% 3.49/3.74  thf('13', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.49/3.74      inference('demod', [status(thm)], ['7', '12'])).
% 3.49/3.74  thf('14', plain,
% 3.49/3.74      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.49/3.74      inference('sup+', [status(thm)], ['3', '13'])).
% 3.49/3.74  thf('15', plain,
% 3.49/3.74      (![X25 : $i]:
% 3.49/3.74         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 3.49/3.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 3.49/3.74      inference('demod', [status(thm)], ['8', '9'])).
% 3.49/3.74  thf('16', plain,
% 3.49/3.74      (![X0 : $i]:
% 3.49/3.74         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 3.49/3.74          | ~ (v1_xboole_0 @ X0))),
% 3.49/3.74      inference('sup+', [status(thm)], ['14', '15'])).
% 3.49/3.74  thf(redefinition_r2_relset_1, axiom,
% 3.49/3.74    (![A:$i,B:$i,C:$i,D:$i]:
% 3.49/3.74     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.49/3.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.49/3.74       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.49/3.74  thf('17', plain,
% 3.49/3.74      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.49/3.74         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 3.49/3.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 3.49/3.74          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 3.49/3.74          | ((X15) != (X18)))),
% 3.49/3.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.49/3.74  thf('18', plain,
% 3.49/3.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.49/3.74         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 3.49/3.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.49/3.74      inference('simplify', [status(thm)], ['17'])).
% 3.49/3.74  thf('19', plain,
% 3.49/3.74      (![X0 : $i]:
% 3.49/3.74         (~ (v1_xboole_0 @ X0)
% 3.49/3.74          | (r2_relset_1 @ X0 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.49/3.74      inference('sup-', [status(thm)], ['16', '18'])).
% 3.49/3.74  thf('20', plain,
% 3.49/3.74      (![X0 : $i, X1 : $i]:
% 3.49/3.74         ((r2_relset_1 @ X1 @ X1 @ X0 @ k1_xboole_0)
% 3.49/3.74          | ~ (v1_xboole_0 @ X0)
% 3.49/3.74          | ~ (v1_xboole_0 @ X1))),
% 3.49/3.74      inference('sup+', [status(thm)], ['2', '19'])).
% 3.49/3.74  thf('21', plain,
% 3.49/3.74      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.49/3.74      inference('sup-', [status(thm)], ['0', '1'])).
% 3.49/3.74  thf('22', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.49/3.74      inference('demod', [status(thm)], ['7', '12'])).
% 3.49/3.74  thf(t67_funct_1, axiom,
% 3.49/3.74    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 3.49/3.74  thf('23', plain,
% 3.49/3.74      (![X5 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X5)) = (k6_relat_1 @ X5))),
% 3.49/3.74      inference('cnf', [status(esa)], [t67_funct_1])).
% 3.49/3.74  thf('24', plain, (((k2_funct_1 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 3.49/3.74      inference('sup+', [status(thm)], ['22', '23'])).
% 3.49/3.74  thf('25', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.49/3.74      inference('demod', [status(thm)], ['7', '12'])).
% 3.49/3.74  thf('26', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.49/3.74      inference('sup+', [status(thm)], ['24', '25'])).
% 3.49/3.74  thf('27', plain,
% 3.49/3.74      (![X0 : $i]: (((k2_funct_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.49/3.74      inference('sup+', [status(thm)], ['21', '26'])).
% 3.49/3.74  thf(t87_funct_2, conjecture,
% 3.49/3.74    (![A:$i,B:$i]:
% 3.49/3.74     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.49/3.74         ( v3_funct_2 @ B @ A @ A ) & 
% 3.49/3.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.49/3.74       ( ![C:$i]:
% 3.49/3.74         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 3.49/3.74             ( v3_funct_2 @ C @ A @ A ) & 
% 3.49/3.74             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.49/3.74           ( ( r2_relset_1 @
% 3.49/3.74               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 3.49/3.74               ( k6_partfun1 @ A ) ) =>
% 3.49/3.74             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 3.49/3.74  thf(zf_stmt_0, negated_conjecture,
% 3.49/3.74    (~( ![A:$i,B:$i]:
% 3.49/3.74        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.49/3.74            ( v3_funct_2 @ B @ A @ A ) & 
% 3.49/3.74            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.49/3.74          ( ![C:$i]:
% 3.49/3.74            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 3.49/3.74                ( v3_funct_2 @ C @ A @ A ) & 
% 3.49/3.74                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.49/3.74              ( ( r2_relset_1 @
% 3.49/3.74                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 3.49/3.74                  ( k6_partfun1 @ A ) ) =>
% 3.49/3.74                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 3.49/3.74    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 3.49/3.74  thf('28', plain,
% 3.49/3.74      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('29', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf(redefinition_k2_funct_2, axiom,
% 3.49/3.74    (![A:$i,B:$i]:
% 3.49/3.74     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.49/3.74         ( v3_funct_2 @ B @ A @ A ) & 
% 3.49/3.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.49/3.74       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 3.49/3.74  thf('30', plain,
% 3.49/3.74      (![X26 : $i, X27 : $i]:
% 3.49/3.74         (((k2_funct_2 @ X27 @ X26) = (k2_funct_1 @ X26))
% 3.49/3.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))
% 3.49/3.74          | ~ (v3_funct_2 @ X26 @ X27 @ X27)
% 3.49/3.74          | ~ (v1_funct_2 @ X26 @ X27 @ X27)
% 3.49/3.74          | ~ (v1_funct_1 @ X26))),
% 3.49/3.74      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 3.49/3.74  thf('31', plain,
% 3.49/3.74      ((~ (v1_funct_1 @ sk_B)
% 3.49/3.74        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.49/3.74        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.49/3.74        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 3.49/3.74      inference('sup-', [status(thm)], ['29', '30'])).
% 3.49/3.74  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('33', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('34', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('35', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.49/3.74      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 3.49/3.74  thf('36', plain,
% 3.49/3.74      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 3.49/3.74      inference('demod', [status(thm)], ['28', '35'])).
% 3.49/3.74  thf('37', plain,
% 3.49/3.74      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ k1_xboole_0)
% 3.49/3.74        | ~ (v1_xboole_0 @ sk_B))),
% 3.49/3.74      inference('sup-', [status(thm)], ['27', '36'])).
% 3.49/3.74  thf('38', plain,
% 3.49/3.74      ((~ (v1_xboole_0 @ sk_A)
% 3.49/3.74        | ~ (v1_xboole_0 @ sk_C)
% 3.49/3.74        | ~ (v1_xboole_0 @ sk_B))),
% 3.49/3.74      inference('sup-', [status(thm)], ['20', '37'])).
% 3.49/3.74  thf('39', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf(cc2_funct_2, axiom,
% 3.49/3.74    (![A:$i,B:$i,C:$i]:
% 3.49/3.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.49/3.74       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 3.49/3.74         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 3.49/3.74  thf('40', plain,
% 3.49/3.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.49/3.74         (~ (v1_funct_1 @ X19)
% 3.49/3.74          | ~ (v3_funct_2 @ X19 @ X20 @ X21)
% 3.49/3.74          | (v2_funct_2 @ X19 @ X21)
% 3.49/3.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.49/3.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 3.49/3.74  thf('41', plain,
% 3.49/3.74      (((v2_funct_2 @ sk_B @ sk_A)
% 3.49/3.74        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.49/3.74        | ~ (v1_funct_1 @ sk_B))),
% 3.49/3.74      inference('sup-', [status(thm)], ['39', '40'])).
% 3.49/3.74  thf('42', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('44', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 3.49/3.74      inference('demod', [status(thm)], ['41', '42', '43'])).
% 3.49/3.74  thf(d3_funct_2, axiom,
% 3.49/3.74    (![A:$i,B:$i]:
% 3.49/3.74     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.49/3.74       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.49/3.74  thf('45', plain,
% 3.49/3.74      (![X22 : $i, X23 : $i]:
% 3.49/3.74         (~ (v2_funct_2 @ X23 @ X22)
% 3.49/3.74          | ((k2_relat_1 @ X23) = (X22))
% 3.49/3.74          | ~ (v5_relat_1 @ X23 @ X22)
% 3.49/3.74          | ~ (v1_relat_1 @ X23))),
% 3.49/3.74      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.49/3.74  thf('46', plain,
% 3.49/3.74      ((~ (v1_relat_1 @ sk_B)
% 3.49/3.74        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 3.49/3.74        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 3.49/3.74      inference('sup-', [status(thm)], ['44', '45'])).
% 3.49/3.74  thf('47', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('48', plain,
% 3.49/3.74      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.49/3.74         ((v1_relat_1 @ X6)
% 3.49/3.74          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 3.49/3.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.49/3.74  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 3.49/3.74      inference('sup-', [status(thm)], ['47', '48'])).
% 3.49/3.74  thf('50', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf(cc2_relset_1, axiom,
% 3.49/3.74    (![A:$i,B:$i,C:$i]:
% 3.49/3.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.49/3.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.49/3.74  thf('51', plain,
% 3.49/3.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.49/3.74         ((v5_relat_1 @ X9 @ X11)
% 3.49/3.74          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.49/3.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.49/3.74  thf('52', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 3.49/3.74      inference('sup-', [status(thm)], ['50', '51'])).
% 3.49/3.74  thf('53', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 3.49/3.74      inference('demod', [status(thm)], ['46', '49', '52'])).
% 3.49/3.74  thf('54', plain,
% 3.49/3.74      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.49/3.74      inference('sup-', [status(thm)], ['0', '1'])).
% 3.49/3.74  thf('55', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.49/3.74      inference('demod', [status(thm)], ['7', '12'])).
% 3.49/3.74  thf('56', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 3.49/3.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.49/3.74  thf('57', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.49/3.74      inference('sup+', [status(thm)], ['55', '56'])).
% 3.49/3.74  thf('58', plain,
% 3.49/3.74      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.49/3.74      inference('sup+', [status(thm)], ['54', '57'])).
% 3.49/3.74  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.49/3.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.49/3.74  thf('60', plain,
% 3.49/3.74      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.49/3.74      inference('sup+', [status(thm)], ['58', '59'])).
% 3.49/3.74  thf('61', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_B))),
% 3.49/3.74      inference('sup+', [status(thm)], ['53', '60'])).
% 3.49/3.74  thf('62', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_C))),
% 3.49/3.74      inference('clc', [status(thm)], ['38', '61'])).
% 3.49/3.74  thf('63', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 3.49/3.74      inference('demod', [status(thm)], ['46', '49', '52'])).
% 3.49/3.74  thf('64', plain,
% 3.49/3.74      (![X2 : $i]:
% 3.49/3.74         (((k2_relat_1 @ X2) != (k1_xboole_0))
% 3.49/3.74          | ((X2) = (k1_xboole_0))
% 3.49/3.74          | ~ (v1_relat_1 @ X2))),
% 3.49/3.74      inference('cnf', [status(esa)], [t64_relat_1])).
% 3.49/3.74  thf('65', plain,
% 3.49/3.74      ((((sk_A) != (k1_xboole_0))
% 3.49/3.74        | ~ (v1_relat_1 @ sk_B)
% 3.49/3.74        | ((sk_B) = (k1_xboole_0)))),
% 3.49/3.74      inference('sup-', [status(thm)], ['63', '64'])).
% 3.49/3.74  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 3.49/3.74      inference('sup-', [status(thm)], ['47', '48'])).
% 3.49/3.74  thf('67', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 3.49/3.74      inference('demod', [status(thm)], ['65', '66'])).
% 3.49/3.74  thf('68', plain,
% 3.49/3.74      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.49/3.74        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 3.49/3.74        (k6_partfun1 @ sk_A))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('69', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 3.49/3.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.49/3.74  thf('70', plain,
% 3.49/3.74      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.49/3.74        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 3.49/3.74        (k6_relat_1 @ sk_A))),
% 3.49/3.74      inference('demod', [status(thm)], ['68', '69'])).
% 3.49/3.74  thf('71', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf(t36_funct_2, axiom,
% 3.49/3.74    (![A:$i,B:$i,C:$i]:
% 3.49/3.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.49/3.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.49/3.74       ( ![D:$i]:
% 3.49/3.74         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.49/3.74             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.49/3.74           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.49/3.74               ( r2_relset_1 @
% 3.49/3.74                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.49/3.74                 ( k6_partfun1 @ A ) ) & 
% 3.49/3.74               ( v2_funct_1 @ C ) ) =>
% 3.49/3.74             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.49/3.74               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 3.49/3.74  thf('72', plain,
% 3.49/3.74      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.49/3.74         (~ (v1_funct_1 @ X33)
% 3.49/3.74          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 3.49/3.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.49/3.74          | ((X33) = (k2_funct_1 @ X36))
% 3.49/3.74          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 3.49/3.74               (k1_partfun1 @ X35 @ X34 @ X34 @ X35 @ X36 @ X33) @ 
% 3.49/3.74               (k6_partfun1 @ X35))
% 3.49/3.74          | ((X34) = (k1_xboole_0))
% 3.49/3.74          | ((X35) = (k1_xboole_0))
% 3.49/3.74          | ~ (v2_funct_1 @ X36)
% 3.49/3.74          | ((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 3.49/3.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 3.49/3.74          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 3.49/3.74          | ~ (v1_funct_1 @ X36))),
% 3.49/3.74      inference('cnf', [status(esa)], [t36_funct_2])).
% 3.49/3.74  thf('73', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 3.49/3.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.49/3.74  thf('74', plain,
% 3.49/3.74      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.49/3.74         (~ (v1_funct_1 @ X33)
% 3.49/3.74          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 3.49/3.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.49/3.74          | ((X33) = (k2_funct_1 @ X36))
% 3.49/3.74          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 3.49/3.74               (k1_partfun1 @ X35 @ X34 @ X34 @ X35 @ X36 @ X33) @ 
% 3.49/3.74               (k6_relat_1 @ X35))
% 3.49/3.74          | ((X34) = (k1_xboole_0))
% 3.49/3.74          | ((X35) = (k1_xboole_0))
% 3.49/3.74          | ~ (v2_funct_1 @ X36)
% 3.49/3.74          | ((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 3.49/3.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 3.49/3.74          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 3.49/3.74          | ~ (v1_funct_1 @ X36))),
% 3.49/3.74      inference('demod', [status(thm)], ['72', '73'])).
% 3.49/3.74  thf('75', plain,
% 3.49/3.74      (![X0 : $i]:
% 3.49/3.74         (~ (v1_funct_1 @ X0)
% 3.49/3.74          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 3.49/3.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.49/3.74          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 3.49/3.74          | ~ (v2_funct_1 @ X0)
% 3.49/3.74          | ((sk_A) = (k1_xboole_0))
% 3.49/3.74          | ((sk_A) = (k1_xboole_0))
% 3.49/3.74          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.49/3.74               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 3.49/3.74               (k6_relat_1 @ sk_A))
% 3.49/3.74          | ((sk_C) = (k2_funct_1 @ X0))
% 3.49/3.74          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 3.49/3.74          | ~ (v1_funct_1 @ sk_C))),
% 3.49/3.74      inference('sup-', [status(thm)], ['71', '74'])).
% 3.49/3.74  thf('76', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('78', plain,
% 3.49/3.74      (![X0 : $i]:
% 3.49/3.74         (~ (v1_funct_1 @ X0)
% 3.49/3.74          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 3.49/3.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.49/3.74          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 3.49/3.74          | ~ (v2_funct_1 @ X0)
% 3.49/3.74          | ((sk_A) = (k1_xboole_0))
% 3.49/3.74          | ((sk_A) = (k1_xboole_0))
% 3.49/3.74          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.49/3.74               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 3.49/3.74               (k6_relat_1 @ sk_A))
% 3.49/3.74          | ((sk_C) = (k2_funct_1 @ X0)))),
% 3.49/3.74      inference('demod', [status(thm)], ['75', '76', '77'])).
% 3.49/3.74  thf('79', plain,
% 3.49/3.74      (![X0 : $i]:
% 3.49/3.74         (((sk_C) = (k2_funct_1 @ X0))
% 3.49/3.74          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.49/3.74               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 3.49/3.74               (k6_relat_1 @ sk_A))
% 3.49/3.74          | ((sk_A) = (k1_xboole_0))
% 3.49/3.74          | ~ (v2_funct_1 @ X0)
% 3.49/3.74          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 3.49/3.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.49/3.74          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 3.49/3.74          | ~ (v1_funct_1 @ X0))),
% 3.49/3.74      inference('simplify', [status(thm)], ['78'])).
% 3.49/3.74  thf('80', plain,
% 3.49/3.74      ((~ (v1_funct_1 @ sk_B)
% 3.49/3.74        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.49/3.74        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.49/3.74        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 3.49/3.74        | ~ (v2_funct_1 @ sk_B)
% 3.49/3.74        | ((sk_A) = (k1_xboole_0))
% 3.49/3.74        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 3.49/3.74      inference('sup-', [status(thm)], ['70', '79'])).
% 3.49/3.74  thf('81', plain, ((v1_funct_1 @ sk_B)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('82', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('83', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('84', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf(redefinition_k2_relset_1, axiom,
% 3.49/3.74    (![A:$i,B:$i,C:$i]:
% 3.49/3.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.49/3.74       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.49/3.74  thf('85', plain,
% 3.49/3.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.49/3.74         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 3.49/3.74          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.49/3.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.49/3.74  thf('86', plain,
% 3.49/3.74      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 3.49/3.74      inference('sup-', [status(thm)], ['84', '85'])).
% 3.49/3.74  thf('87', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 3.49/3.74      inference('demod', [status(thm)], ['46', '49', '52'])).
% 3.49/3.74  thf('88', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 3.49/3.74      inference('demod', [status(thm)], ['86', '87'])).
% 3.49/3.74  thf('89', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('90', plain,
% 3.49/3.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.49/3.74         (~ (v1_funct_1 @ X19)
% 3.49/3.74          | ~ (v3_funct_2 @ X19 @ X20 @ X21)
% 3.49/3.74          | (v2_funct_1 @ X19)
% 3.49/3.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.49/3.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 3.49/3.74  thf('91', plain,
% 3.49/3.74      (((v2_funct_1 @ sk_B)
% 3.49/3.74        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.49/3.74        | ~ (v1_funct_1 @ sk_B))),
% 3.49/3.74      inference('sup-', [status(thm)], ['89', '90'])).
% 3.49/3.74  thf('92', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('93', plain, ((v1_funct_1 @ sk_B)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('94', plain, ((v2_funct_1 @ sk_B)),
% 3.49/3.74      inference('demod', [status(thm)], ['91', '92', '93'])).
% 3.49/3.74  thf('95', plain,
% 3.49/3.74      ((((sk_A) != (sk_A))
% 3.49/3.74        | ((sk_A) = (k1_xboole_0))
% 3.49/3.74        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 3.49/3.74      inference('demod', [status(thm)], ['80', '81', '82', '83', '88', '94'])).
% 3.49/3.74  thf('96', plain,
% 3.49/3.74      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 3.49/3.74      inference('simplify', [status(thm)], ['95'])).
% 3.49/3.74  thf('97', plain,
% 3.49/3.74      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 3.49/3.74      inference('demod', [status(thm)], ['28', '35'])).
% 3.49/3.74  thf('98', plain,
% 3.49/3.74      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.49/3.74      inference('sup-', [status(thm)], ['96', '97'])).
% 3.49/3.74  thf('99', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('100', plain,
% 3.49/3.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.49/3.74         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 3.49/3.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.49/3.74      inference('simplify', [status(thm)], ['17'])).
% 3.49/3.74  thf('101', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 3.49/3.74      inference('sup-', [status(thm)], ['99', '100'])).
% 3.49/3.74  thf('102', plain, (((sk_A) = (k1_xboole_0))),
% 3.49/3.74      inference('demod', [status(thm)], ['98', '101'])).
% 3.49/3.74  thf('103', plain,
% 3.49/3.74      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 3.49/3.74      inference('demod', [status(thm)], ['67', '102'])).
% 3.49/3.74  thf('104', plain, (((sk_B) = (k1_xboole_0))),
% 3.49/3.74      inference('simplify', [status(thm)], ['103'])).
% 3.49/3.74  thf('105', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.49/3.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.49/3.74  thf('106', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.49/3.74      inference('demod', [status(thm)], ['62', '104', '105'])).
% 3.49/3.74  thf('107', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('108', plain,
% 3.49/3.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.49/3.74         (~ (v1_funct_1 @ X19)
% 3.49/3.74          | ~ (v3_funct_2 @ X19 @ X20 @ X21)
% 3.49/3.74          | (v2_funct_2 @ X19 @ X21)
% 3.49/3.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.49/3.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 3.49/3.74  thf('109', plain,
% 3.49/3.74      (((v2_funct_2 @ sk_C @ sk_A)
% 3.49/3.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 3.49/3.74        | ~ (v1_funct_1 @ sk_C))),
% 3.49/3.74      inference('sup-', [status(thm)], ['107', '108'])).
% 3.49/3.74  thf('110', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('112', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 3.49/3.74      inference('demod', [status(thm)], ['109', '110', '111'])).
% 3.49/3.74  thf('113', plain,
% 3.49/3.74      (![X22 : $i, X23 : $i]:
% 3.49/3.74         (~ (v2_funct_2 @ X23 @ X22)
% 3.49/3.74          | ((k2_relat_1 @ X23) = (X22))
% 3.49/3.74          | ~ (v5_relat_1 @ X23 @ X22)
% 3.49/3.74          | ~ (v1_relat_1 @ X23))),
% 3.49/3.74      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.49/3.74  thf('114', plain,
% 3.49/3.74      ((~ (v1_relat_1 @ sk_C)
% 3.49/3.74        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 3.49/3.74        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 3.49/3.74      inference('sup-', [status(thm)], ['112', '113'])).
% 3.49/3.74  thf('115', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('116', plain,
% 3.49/3.74      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.49/3.74         ((v1_relat_1 @ X6)
% 3.49/3.74          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 3.49/3.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.49/3.74  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 3.49/3.74      inference('sup-', [status(thm)], ['115', '116'])).
% 3.49/3.74  thf('118', plain,
% 3.49/3.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.49/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.74  thf('119', plain,
% 3.49/3.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.49/3.74         ((v5_relat_1 @ X9 @ X11)
% 3.49/3.74          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.49/3.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.49/3.74  thf('120', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 3.49/3.74      inference('sup-', [status(thm)], ['118', '119'])).
% 3.49/3.74  thf('121', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 3.49/3.74      inference('demod', [status(thm)], ['114', '117', '120'])).
% 3.49/3.74  thf('122', plain,
% 3.49/3.74      (![X2 : $i]:
% 3.49/3.74         (((k2_relat_1 @ X2) != (k1_xboole_0))
% 3.49/3.74          | ((X2) = (k1_xboole_0))
% 3.49/3.74          | ~ (v1_relat_1 @ X2))),
% 3.49/3.74      inference('cnf', [status(esa)], [t64_relat_1])).
% 3.49/3.74  thf('123', plain,
% 3.49/3.74      ((((sk_A) != (k1_xboole_0))
% 3.49/3.74        | ~ (v1_relat_1 @ sk_C)
% 3.49/3.74        | ((sk_C) = (k1_xboole_0)))),
% 3.49/3.74      inference('sup-', [status(thm)], ['121', '122'])).
% 3.49/3.74  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 3.49/3.74      inference('sup-', [status(thm)], ['115', '116'])).
% 3.49/3.74  thf('125', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 3.49/3.74      inference('demod', [status(thm)], ['123', '124'])).
% 3.49/3.74  thf('126', plain, (((sk_A) = (k1_xboole_0))),
% 3.49/3.74      inference('demod', [status(thm)], ['98', '101'])).
% 3.49/3.74  thf('127', plain,
% 3.49/3.74      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 3.49/3.74      inference('demod', [status(thm)], ['125', '126'])).
% 3.49/3.74  thf('128', plain, (((sk_C) = (k1_xboole_0))),
% 3.49/3.74      inference('simplify', [status(thm)], ['127'])).
% 3.49/3.74  thf('129', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.49/3.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.49/3.74  thf('130', plain, ($false),
% 3.49/3.74      inference('demod', [status(thm)], ['106', '128', '129'])).
% 3.49/3.74  
% 3.49/3.74  % SZS output end Refutation
% 3.49/3.74  
% 3.49/3.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
