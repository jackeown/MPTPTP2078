%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NlnTb6aGcP

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:05 EST 2020

% Result     : Theorem 3.32s
% Output     : Refutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 511 expanded)
%              Number of leaves         :   43 ( 168 expanded)
%              Depth                    :   19
%              Number of atoms          : 1725 (8821 expanded)
%              Number of equality atoms :   79 ( 176 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('9',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('12',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('13',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('17',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('19',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 )
      | ( X30 != X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('20',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_relset_1 @ X31 @ X32 @ X33 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('28',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ X0 @ X0 @ X3 @ X1 @ ( k6_partfun1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ ( k6_partfun1 @ X0 ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('38',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ ( k6_partfun1 @ X0 ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('44',plain,(
    m1_subset_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('50',plain,
    ( k1_xboole_0
    = ( k5_relat_1 @ k1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_C ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('63',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('64',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('65',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('66',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('74',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( r2_relset_1 @ X45 @ X45 @ ( k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47 ) @ ( k6_partfun1 @ X45 ) )
      | ( ( k2_relset_1 @ X46 @ X45 @ X47 )
        = X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('81',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('82',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['79','82','83','84','85'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('87',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k2_relat_1 @ X36 )
       != X35 )
      | ( v2_funct_2 @ X36 @ X35 )
      | ~ ( v5_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('88',plain,(
    ! [X36: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v5_relat_1 @ X36 @ ( k2_relat_1 @ X36 ) )
      | ( v2_funct_2 @ X36 @ ( k2_relat_1 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('91',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('92',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['79','82','83','84','85'])).

thf('94',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('95',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['89','92','93','96'])).

thf('98',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['69'])).

thf('99',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['69'])).

thf('101',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['71','101'])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['61','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('107',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('110',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['103','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('114',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('122',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48 ) )
      | ( v2_funct_1 @ X52 )
      | ( X50 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X49 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('134',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['139','144'])).

thf('146',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','147'])).

thf('149',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('150',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('152',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['131','150','151'])).

thf('153',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['69'])).

thf('154',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('155',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['153','154'])).

thf('156',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['152','155'])).

thf('157',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('158',plain,(
    $false ),
    inference(demod,[status(thm)],['111','156','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NlnTb6aGcP
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:56:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.32/3.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.32/3.61  % Solved by: fo/fo7.sh
% 3.32/3.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.32/3.61  % done 3615 iterations in 3.168s
% 3.32/3.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.32/3.61  % SZS output start Refutation
% 3.32/3.61  thf(sk_C_type, type, sk_C: $i).
% 3.32/3.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.32/3.61  thf(sk_A_type, type, sk_A: $i).
% 3.32/3.61  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.32/3.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.32/3.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.32/3.61  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.32/3.61  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.32/3.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.32/3.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.32/3.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.32/3.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.32/3.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.32/3.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.32/3.61  thf(sk_B_type, type, sk_B: $i).
% 3.32/3.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.32/3.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.32/3.61  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 3.32/3.61  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.32/3.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.32/3.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.32/3.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.32/3.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.32/3.61  thf(sk_D_type, type, sk_D: $i).
% 3.32/3.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.32/3.61  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.32/3.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.32/3.61  thf(t8_boole, axiom,
% 3.32/3.61    (![A:$i,B:$i]:
% 3.32/3.61     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.32/3.61  thf('1', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i]:
% 3.32/3.61         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.32/3.61      inference('cnf', [status(esa)], [t8_boole])).
% 3.32/3.61  thf('2', plain,
% 3.32/3.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup-', [status(thm)], ['0', '1'])).
% 3.32/3.61  thf('3', plain,
% 3.32/3.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup-', [status(thm)], ['0', '1'])).
% 3.32/3.61  thf('4', plain,
% 3.32/3.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup-', [status(thm)], ['0', '1'])).
% 3.32/3.61  thf(t113_zfmisc_1, axiom,
% 3.32/3.61    (![A:$i,B:$i]:
% 3.32/3.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.32/3.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.32/3.61  thf('5', plain,
% 3.32/3.61      (![X3 : $i, X4 : $i]:
% 3.32/3.61         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 3.32/3.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.32/3.61  thf('6', plain,
% 3.32/3.61      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 3.32/3.61      inference('simplify', [status(thm)], ['5'])).
% 3.32/3.61  thf('7', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i]:
% 3.32/3.61         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup+', [status(thm)], ['4', '6'])).
% 3.32/3.61  thf('8', plain,
% 3.32/3.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup-', [status(thm)], ['0', '1'])).
% 3.32/3.61  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.32/3.61  thf('9', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.32/3.61      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.32/3.61  thf(redefinition_k6_partfun1, axiom,
% 3.32/3.61    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.32/3.61  thf('10', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 3.32/3.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.32/3.61  thf('11', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.32/3.61      inference('demod', [status(thm)], ['9', '10'])).
% 3.32/3.61  thf(t29_relset_1, axiom,
% 3.32/3.61    (![A:$i]:
% 3.32/3.61     ( m1_subset_1 @
% 3.32/3.61       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.32/3.61  thf('12', plain,
% 3.32/3.61      (![X34 : $i]:
% 3.32/3.61         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 3.32/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 3.32/3.61      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.32/3.61  thf('13', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 3.32/3.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.32/3.61  thf('14', plain,
% 3.32/3.61      (![X34 : $i]:
% 3.32/3.61         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 3.32/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 3.32/3.61      inference('demod', [status(thm)], ['12', '13'])).
% 3.32/3.61  thf('15', plain,
% 3.32/3.61      ((m1_subset_1 @ k1_xboole_0 @ 
% 3.32/3.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.32/3.61      inference('sup+', [status(thm)], ['11', '14'])).
% 3.32/3.61  thf('16', plain,
% 3.32/3.61      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 3.32/3.61      inference('simplify', [status(thm)], ['5'])).
% 3.32/3.61  thf('17', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.32/3.61      inference('demod', [status(thm)], ['15', '16'])).
% 3.32/3.61  thf('18', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 3.32/3.61          | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup+', [status(thm)], ['8', '17'])).
% 3.32/3.61  thf(redefinition_r2_relset_1, axiom,
% 3.32/3.61    (![A:$i,B:$i,C:$i,D:$i]:
% 3.32/3.61     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.32/3.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.32/3.61       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.32/3.61  thf('19', plain,
% 3.32/3.61      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.32/3.61         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.32/3.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.32/3.61          | (r2_relset_1 @ X31 @ X32 @ X30 @ X33)
% 3.32/3.61          | ((X30) != (X33)))),
% 3.32/3.61      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.32/3.61  thf('20', plain,
% 3.32/3.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.32/3.61         ((r2_relset_1 @ X31 @ X32 @ X33 @ X33)
% 3.32/3.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 3.32/3.61      inference('simplify', [status(thm)], ['19'])).
% 3.32/3.61  thf('21', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i]:
% 3.32/3.61         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.32/3.61          | (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.32/3.61      inference('sup-', [status(thm)], ['18', '20'])).
% 3.32/3.61  thf('22', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i]:
% 3.32/3.61         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.32/3.61          | ~ (v1_xboole_0 @ X1)
% 3.32/3.61          | (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.32/3.61      inference('sup-', [status(thm)], ['7', '21'])).
% 3.32/3.61  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.32/3.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.32/3.61  thf('24', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i]:
% 3.32/3.61         (~ (v1_xboole_0 @ X1)
% 3.32/3.61          | (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.32/3.61      inference('demod', [status(thm)], ['22', '23'])).
% 3.32/3.61  thf('25', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.61         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 3.32/3.61          | ~ (v1_xboole_0 @ X0)
% 3.32/3.61          | ~ (v1_xboole_0 @ X2))),
% 3.32/3.61      inference('sup+', [status(thm)], ['3', '24'])).
% 3.32/3.61  thf('26', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.32/3.61         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 3.32/3.61          | ~ (v1_xboole_0 @ X0)
% 3.32/3.61          | ~ (v1_xboole_0 @ X3)
% 3.32/3.61          | ~ (v1_xboole_0 @ X1))),
% 3.32/3.61      inference('sup+', [status(thm)], ['2', '25'])).
% 3.32/3.61  thf('27', plain,
% 3.32/3.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup-', [status(thm)], ['0', '1'])).
% 3.32/3.61  thf('28', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.32/3.61      inference('demod', [status(thm)], ['9', '10'])).
% 3.32/3.61  thf('29', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         (((k6_partfun1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup+', [status(thm)], ['27', '28'])).
% 3.32/3.61  thf('30', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.32/3.61      inference('demod', [status(thm)], ['9', '10'])).
% 3.32/3.61  thf(t29_funct_2, conjecture,
% 3.32/3.61    (![A:$i,B:$i,C:$i]:
% 3.32/3.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.32/3.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.32/3.61       ( ![D:$i]:
% 3.32/3.61         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.32/3.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.32/3.61           ( ( r2_relset_1 @
% 3.32/3.61               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.32/3.61               ( k6_partfun1 @ A ) ) =>
% 3.32/3.61             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.32/3.61  thf(zf_stmt_0, negated_conjecture,
% 3.32/3.61    (~( ![A:$i,B:$i,C:$i]:
% 3.32/3.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.32/3.61            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.32/3.61          ( ![D:$i]:
% 3.32/3.61            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.32/3.61                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.32/3.61              ( ( r2_relset_1 @
% 3.32/3.61                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.32/3.61                  ( k6_partfun1 @ A ) ) =>
% 3.32/3.61                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.32/3.61    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.32/3.61  thf('31', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('32', plain,
% 3.32/3.61      (![X34 : $i]:
% 3.32/3.61         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 3.32/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 3.32/3.61      inference('demod', [status(thm)], ['12', '13'])).
% 3.32/3.61  thf(dt_k4_relset_1, axiom,
% 3.32/3.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.32/3.61     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.32/3.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.32/3.61       ( m1_subset_1 @
% 3.32/3.61         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.32/3.61         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 3.32/3.61  thf('33', plain,
% 3.32/3.61      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.32/3.61         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 3.32/3.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 3.32/3.61          | (m1_subset_1 @ (k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18) @ 
% 3.32/3.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X20))))),
% 3.32/3.61      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 3.32/3.61  thf('34', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.32/3.61         ((m1_subset_1 @ 
% 3.32/3.61           (k4_relset_1 @ X0 @ X0 @ X3 @ X1 @ (k6_partfun1 @ X0) @ X2) @ 
% 3.32/3.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 3.32/3.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1))))),
% 3.32/3.61      inference('sup-', [status(thm)], ['32', '33'])).
% 3.32/3.61  thf('35', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         (m1_subset_1 @ 
% 3.32/3.61          (k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ (k6_partfun1 @ X0) @ sk_C) @ 
% 3.32/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 3.32/3.61      inference('sup-', [status(thm)], ['31', '34'])).
% 3.32/3.61  thf('36', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('37', plain,
% 3.32/3.61      (![X34 : $i]:
% 3.32/3.61         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 3.32/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 3.32/3.61      inference('demod', [status(thm)], ['12', '13'])).
% 3.32/3.61  thf(redefinition_k4_relset_1, axiom,
% 3.32/3.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.32/3.61     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.32/3.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.32/3.61       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.32/3.61  thf('38', plain,
% 3.32/3.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.32/3.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.32/3.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.32/3.61          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 3.32/3.61              = (k5_relat_1 @ X24 @ X27)))),
% 3.32/3.61      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 3.32/3.61  thf('39', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.32/3.61         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_partfun1 @ X0) @ X1)
% 3.32/3.61            = (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 3.32/3.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 3.32/3.61      inference('sup-', [status(thm)], ['37', '38'])).
% 3.32/3.61  thf('40', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ (k6_partfun1 @ X0) @ sk_C)
% 3.32/3.61           = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_C))),
% 3.32/3.61      inference('sup-', [status(thm)], ['36', '39'])).
% 3.32/3.61  thf('41', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         (m1_subset_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_C) @ 
% 3.32/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 3.32/3.61      inference('demod', [status(thm)], ['35', '40'])).
% 3.32/3.61  thf('42', plain,
% 3.32/3.61      ((m1_subset_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_C) @ 
% 3.32/3.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B)))),
% 3.32/3.61      inference('sup+', [status(thm)], ['30', '41'])).
% 3.32/3.61  thf('43', plain,
% 3.32/3.61      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 3.32/3.61      inference('simplify', [status(thm)], ['5'])).
% 3.32/3.61  thf('44', plain,
% 3.32/3.61      ((m1_subset_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_C) @ 
% 3.32/3.61        (k1_zfmisc_1 @ k1_xboole_0))),
% 3.32/3.61      inference('demod', [status(thm)], ['42', '43'])).
% 3.32/3.61  thf(cc1_subset_1, axiom,
% 3.32/3.61    (![A:$i]:
% 3.32/3.61     ( ( v1_xboole_0 @ A ) =>
% 3.32/3.61       ( ![B:$i]:
% 3.32/3.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.32/3.61  thf('45', plain,
% 3.32/3.61      (![X5 : $i, X6 : $i]:
% 3.32/3.61         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 3.32/3.61          | (v1_xboole_0 @ X5)
% 3.32/3.61          | ~ (v1_xboole_0 @ X6))),
% 3.32/3.61      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.32/3.61  thf('46', plain,
% 3.32/3.61      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.32/3.61        | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_C)))),
% 3.32/3.61      inference('sup-', [status(thm)], ['44', '45'])).
% 3.32/3.61  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.32/3.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.32/3.61  thf('48', plain, ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_C))),
% 3.32/3.61      inference('demod', [status(thm)], ['46', '47'])).
% 3.32/3.61  thf('49', plain,
% 3.32/3.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup-', [status(thm)], ['0', '1'])).
% 3.32/3.61  thf('50', plain, (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ sk_C))),
% 3.32/3.61      inference('sup-', [status(thm)], ['48', '49'])).
% 3.32/3.61  thf('51', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         (((k1_xboole_0) = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_C))
% 3.32/3.61          | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup+', [status(thm)], ['29', '50'])).
% 3.32/3.61  thf('52', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         (m1_subset_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_C) @ 
% 3.32/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 3.32/3.61      inference('demod', [status(thm)], ['35', '40'])).
% 3.32/3.61  thf('53', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         ((m1_subset_1 @ k1_xboole_0 @ 
% 3.32/3.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 3.32/3.61          | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup+', [status(thm)], ['51', '52'])).
% 3.32/3.61  thf('54', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('55', plain,
% 3.32/3.61      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.32/3.61         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.32/3.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.32/3.61          | ((X30) = (X33))
% 3.32/3.61          | ~ (r2_relset_1 @ X31 @ X32 @ X30 @ X33))),
% 3.32/3.61      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.32/3.61  thf('56', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ X0)
% 3.32/3.61          | ((sk_C) = (X0))
% 3.32/3.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 3.32/3.61      inference('sup-', [status(thm)], ['54', '55'])).
% 3.32/3.61  thf('57', plain,
% 3.32/3.61      ((~ (v1_xboole_0 @ sk_A)
% 3.32/3.61        | ((sk_C) = (k1_xboole_0))
% 3.32/3.61        | ~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ k1_xboole_0))),
% 3.32/3.61      inference('sup-', [status(thm)], ['53', '56'])).
% 3.32/3.61  thf('58', plain,
% 3.32/3.61      ((~ (v1_xboole_0 @ sk_C)
% 3.32/3.61        | ~ (v1_xboole_0 @ sk_A)
% 3.32/3.61        | ~ (v1_xboole_0 @ k1_xboole_0)
% 3.32/3.61        | ((sk_C) = (k1_xboole_0))
% 3.32/3.61        | ~ (v1_xboole_0 @ sk_A))),
% 3.32/3.61      inference('sup-', [status(thm)], ['26', '57'])).
% 3.32/3.61  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.32/3.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.32/3.61  thf('60', plain,
% 3.32/3.61      ((~ (v1_xboole_0 @ sk_C)
% 3.32/3.61        | ~ (v1_xboole_0 @ sk_A)
% 3.32/3.61        | ((sk_C) = (k1_xboole_0))
% 3.32/3.61        | ~ (v1_xboole_0 @ sk_A))),
% 3.32/3.61      inference('demod', [status(thm)], ['58', '59'])).
% 3.32/3.61  thf('61', plain,
% 3.32/3.61      ((((sk_C) = (k1_xboole_0))
% 3.32/3.61        | ~ (v1_xboole_0 @ sk_A)
% 3.32/3.61        | ~ (v1_xboole_0 @ sk_C))),
% 3.32/3.61      inference('simplify', [status(thm)], ['60'])).
% 3.32/3.61  thf('62', plain,
% 3.32/3.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup-', [status(thm)], ['0', '1'])).
% 3.32/3.61  thf('63', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.32/3.61      inference('demod', [status(thm)], ['9', '10'])).
% 3.32/3.61  thf(fc4_funct_1, axiom,
% 3.32/3.61    (![A:$i]:
% 3.32/3.61     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.32/3.61       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.32/3.61  thf('64', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 3.32/3.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.32/3.61  thf('65', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 3.32/3.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.32/3.61  thf('66', plain, (![X8 : $i]: (v2_funct_1 @ (k6_partfun1 @ X8))),
% 3.32/3.61      inference('demod', [status(thm)], ['64', '65'])).
% 3.32/3.61  thf('67', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.32/3.61      inference('sup+', [status(thm)], ['63', '66'])).
% 3.32/3.61  thf('68', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup+', [status(thm)], ['62', '67'])).
% 3.32/3.61  thf('69', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('70', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.32/3.61      inference('split', [status(esa)], ['69'])).
% 3.32/3.61  thf('71', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.32/3.61      inference('sup-', [status(thm)], ['68', '70'])).
% 3.32/3.61  thf('72', plain,
% 3.32/3.61      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.32/3.61        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.32/3.61        (k6_partfun1 @ sk_A))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('73', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf(t24_funct_2, axiom,
% 3.32/3.61    (![A:$i,B:$i,C:$i]:
% 3.32/3.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.32/3.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.32/3.61       ( ![D:$i]:
% 3.32/3.61         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.32/3.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.32/3.61           ( ( r2_relset_1 @
% 3.32/3.61               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.32/3.61               ( k6_partfun1 @ B ) ) =>
% 3.32/3.61             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.32/3.61  thf('74', plain,
% 3.32/3.61      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 3.32/3.61         (~ (v1_funct_1 @ X44)
% 3.32/3.61          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 3.32/3.61          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 3.32/3.61          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 3.32/3.61               (k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47) @ 
% 3.32/3.61               (k6_partfun1 @ X45))
% 3.32/3.61          | ((k2_relset_1 @ X46 @ X45 @ X47) = (X45))
% 3.32/3.61          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 3.32/3.61          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 3.32/3.61          | ~ (v1_funct_1 @ X47))),
% 3.32/3.61      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.32/3.61  thf('75', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         (~ (v1_funct_1 @ X0)
% 3.32/3.61          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.32/3.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.32/3.61          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.32/3.61          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.32/3.61               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.32/3.61               (k6_partfun1 @ sk_A))
% 3.32/3.61          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.32/3.61          | ~ (v1_funct_1 @ sk_C))),
% 3.32/3.61      inference('sup-', [status(thm)], ['73', '74'])).
% 3.32/3.61  thf('76', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('78', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         (~ (v1_funct_1 @ X0)
% 3.32/3.61          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.32/3.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.32/3.61          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.32/3.61          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.32/3.61               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.32/3.61               (k6_partfun1 @ sk_A)))),
% 3.32/3.61      inference('demod', [status(thm)], ['75', '76', '77'])).
% 3.32/3.61  thf('79', plain,
% 3.32/3.61      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.32/3.61        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.32/3.61        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.32/3.61        | ~ (v1_funct_1 @ sk_D))),
% 3.32/3.61      inference('sup-', [status(thm)], ['72', '78'])).
% 3.32/3.61  thf('80', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf(redefinition_k2_relset_1, axiom,
% 3.32/3.61    (![A:$i,B:$i,C:$i]:
% 3.32/3.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.32/3.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.32/3.61  thf('81', plain,
% 3.32/3.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.32/3.61         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 3.32/3.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.32/3.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.32/3.61  thf('82', plain,
% 3.32/3.61      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.32/3.61      inference('sup-', [status(thm)], ['80', '81'])).
% 3.32/3.61  thf('83', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('84', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('86', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.32/3.61      inference('demod', [status(thm)], ['79', '82', '83', '84', '85'])).
% 3.32/3.61  thf(d3_funct_2, axiom,
% 3.32/3.61    (![A:$i,B:$i]:
% 3.32/3.61     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.32/3.61       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.32/3.61  thf('87', plain,
% 3.32/3.61      (![X35 : $i, X36 : $i]:
% 3.32/3.61         (((k2_relat_1 @ X36) != (X35))
% 3.32/3.61          | (v2_funct_2 @ X36 @ X35)
% 3.32/3.61          | ~ (v5_relat_1 @ X36 @ X35)
% 3.32/3.61          | ~ (v1_relat_1 @ X36))),
% 3.32/3.61      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.32/3.61  thf('88', plain,
% 3.32/3.61      (![X36 : $i]:
% 3.32/3.61         (~ (v1_relat_1 @ X36)
% 3.32/3.61          | ~ (v5_relat_1 @ X36 @ (k2_relat_1 @ X36))
% 3.32/3.61          | (v2_funct_2 @ X36 @ (k2_relat_1 @ X36)))),
% 3.32/3.61      inference('simplify', [status(thm)], ['87'])).
% 3.32/3.61  thf('89', plain,
% 3.32/3.61      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.32/3.61        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.32/3.61        | ~ (v1_relat_1 @ sk_D))),
% 3.32/3.61      inference('sup-', [status(thm)], ['86', '88'])).
% 3.32/3.61  thf('90', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf(cc2_relset_1, axiom,
% 3.32/3.61    (![A:$i,B:$i,C:$i]:
% 3.32/3.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.32/3.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.32/3.61  thf('91', plain,
% 3.32/3.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.32/3.61         ((v5_relat_1 @ X12 @ X14)
% 3.32/3.61          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.32/3.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.32/3.61  thf('92', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.32/3.61      inference('sup-', [status(thm)], ['90', '91'])).
% 3.32/3.61  thf('93', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.32/3.61      inference('demod', [status(thm)], ['79', '82', '83', '84', '85'])).
% 3.32/3.61  thf('94', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf(cc1_relset_1, axiom,
% 3.32/3.61    (![A:$i,B:$i,C:$i]:
% 3.32/3.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.32/3.61       ( v1_relat_1 @ C ) ))).
% 3.32/3.61  thf('95', plain,
% 3.32/3.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.32/3.61         ((v1_relat_1 @ X9)
% 3.32/3.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.32/3.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.32/3.61  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 3.32/3.61      inference('sup-', [status(thm)], ['94', '95'])).
% 3.32/3.61  thf('97', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.32/3.61      inference('demod', [status(thm)], ['89', '92', '93', '96'])).
% 3.32/3.61  thf('98', plain,
% 3.32/3.61      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.32/3.61      inference('split', [status(esa)], ['69'])).
% 3.32/3.61  thf('99', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.32/3.61      inference('sup-', [status(thm)], ['97', '98'])).
% 3.32/3.61  thf('100', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.32/3.61      inference('split', [status(esa)], ['69'])).
% 3.32/3.61  thf('101', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.32/3.61      inference('sat_resolution*', [status(thm)], ['99', '100'])).
% 3.32/3.61  thf('102', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.32/3.61      inference('simpl_trail', [status(thm)], ['71', '101'])).
% 3.32/3.61  thf('103', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 3.32/3.61      inference('clc', [status(thm)], ['61', '102'])).
% 3.32/3.61  thf('104', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i]:
% 3.32/3.61         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.32/3.61      inference('sup+', [status(thm)], ['4', '6'])).
% 3.32/3.61  thf('105', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('106', plain,
% 3.32/3.61      (![X5 : $i, X6 : $i]:
% 3.32/3.61         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 3.32/3.61          | (v1_xboole_0 @ X5)
% 3.32/3.61          | ~ (v1_xboole_0 @ X6))),
% 3.32/3.61      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.32/3.61  thf('107', plain,
% 3.32/3.61      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.32/3.61      inference('sup-', [status(thm)], ['105', '106'])).
% 3.32/3.61  thf('108', plain,
% 3.32/3.61      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.32/3.61        | ~ (v1_xboole_0 @ sk_A)
% 3.32/3.61        | (v1_xboole_0 @ sk_C))),
% 3.32/3.61      inference('sup-', [status(thm)], ['104', '107'])).
% 3.32/3.61  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.32/3.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.32/3.61  thf('110', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 3.32/3.61      inference('demod', [status(thm)], ['108', '109'])).
% 3.32/3.61  thf('111', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.32/3.61      inference('clc', [status(thm)], ['103', '110'])).
% 3.32/3.61  thf('112', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('113', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf(redefinition_k1_partfun1, axiom,
% 3.32/3.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.32/3.61     ( ( ( v1_funct_1 @ E ) & 
% 3.32/3.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.32/3.61         ( v1_funct_1 @ F ) & 
% 3.32/3.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.32/3.61       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.32/3.61  thf('114', plain,
% 3.32/3.61      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.32/3.61         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 3.32/3.61          | ~ (v1_funct_1 @ X37)
% 3.32/3.61          | ~ (v1_funct_1 @ X40)
% 3.32/3.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 3.32/3.61          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 3.32/3.61              = (k5_relat_1 @ X37 @ X40)))),
% 3.32/3.61      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.32/3.61  thf('115', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.61         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.32/3.61            = (k5_relat_1 @ sk_C @ X0))
% 3.32/3.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.32/3.61          | ~ (v1_funct_1 @ X0)
% 3.32/3.61          | ~ (v1_funct_1 @ sk_C))),
% 3.32/3.61      inference('sup-', [status(thm)], ['113', '114'])).
% 3.32/3.61  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('117', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.61         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.32/3.61            = (k5_relat_1 @ sk_C @ X0))
% 3.32/3.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.32/3.61          | ~ (v1_funct_1 @ X0))),
% 3.32/3.61      inference('demod', [status(thm)], ['115', '116'])).
% 3.32/3.61  thf('118', plain,
% 3.32/3.61      ((~ (v1_funct_1 @ sk_D)
% 3.32/3.61        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.32/3.61            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.32/3.61      inference('sup-', [status(thm)], ['112', '117'])).
% 3.32/3.61  thf('119', plain, ((v1_funct_1 @ sk_D)),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('120', plain,
% 3.32/3.61      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.32/3.61         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.32/3.61      inference('demod', [status(thm)], ['118', '119'])).
% 3.32/3.61  thf('121', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf(t26_funct_2, axiom,
% 3.32/3.61    (![A:$i,B:$i,C:$i,D:$i]:
% 3.32/3.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.32/3.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.32/3.61       ( ![E:$i]:
% 3.32/3.61         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.32/3.61             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.32/3.61           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.32/3.61             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.32/3.61               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.32/3.61  thf('122', plain,
% 3.32/3.61      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 3.32/3.61         (~ (v1_funct_1 @ X48)
% 3.32/3.61          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 3.32/3.61          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 3.32/3.61          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48))
% 3.32/3.61          | (v2_funct_1 @ X52)
% 3.32/3.61          | ((X50) = (k1_xboole_0))
% 3.32/3.61          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 3.32/3.61          | ~ (v1_funct_2 @ X52 @ X51 @ X49)
% 3.32/3.61          | ~ (v1_funct_1 @ X52))),
% 3.32/3.61      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.32/3.61  thf('123', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i]:
% 3.32/3.61         (~ (v1_funct_1 @ X0)
% 3.32/3.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.32/3.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.32/3.61          | ((sk_A) = (k1_xboole_0))
% 3.32/3.61          | (v2_funct_1 @ X0)
% 3.32/3.61          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.32/3.61          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.32/3.61          | ~ (v1_funct_1 @ sk_D))),
% 3.32/3.61      inference('sup-', [status(thm)], ['121', '122'])).
% 3.32/3.61  thf('124', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('125', plain, ((v1_funct_1 @ sk_D)),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('126', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i]:
% 3.32/3.61         (~ (v1_funct_1 @ X0)
% 3.32/3.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.32/3.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.32/3.61          | ((sk_A) = (k1_xboole_0))
% 3.32/3.61          | (v2_funct_1 @ X0)
% 3.32/3.61          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.32/3.61      inference('demod', [status(thm)], ['123', '124', '125'])).
% 3.32/3.61  thf('127', plain,
% 3.32/3.61      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.32/3.61        | (v2_funct_1 @ sk_C)
% 3.32/3.61        | ((sk_A) = (k1_xboole_0))
% 3.32/3.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.32/3.61        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.32/3.61        | ~ (v1_funct_1 @ sk_C))),
% 3.32/3.61      inference('sup-', [status(thm)], ['120', '126'])).
% 3.32/3.61  thf('128', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('129', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('131', plain,
% 3.32/3.61      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.32/3.61        | (v2_funct_1 @ sk_C)
% 3.32/3.61        | ((sk_A) = (k1_xboole_0)))),
% 3.32/3.61      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 3.32/3.61  thf('132', plain,
% 3.32/3.61      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.32/3.61        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.32/3.61        (k6_partfun1 @ sk_A))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('133', plain,
% 3.32/3.61      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.32/3.61         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.32/3.61      inference('demod', [status(thm)], ['118', '119'])).
% 3.32/3.61  thf('134', plain,
% 3.32/3.61      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.32/3.61        (k6_partfun1 @ sk_A))),
% 3.32/3.61      inference('demod', [status(thm)], ['132', '133'])).
% 3.32/3.61  thf('135', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('136', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('137', plain,
% 3.32/3.61      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.32/3.61         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 3.32/3.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 3.32/3.61          | (m1_subset_1 @ (k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18) @ 
% 3.32/3.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X20))))),
% 3.32/3.61      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 3.32/3.61  thf('138', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.61         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.32/3.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.32/3.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 3.32/3.61      inference('sup-', [status(thm)], ['136', '137'])).
% 3.32/3.61  thf('139', plain,
% 3.32/3.61      ((m1_subset_1 @ 
% 3.32/3.61        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.32/3.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.32/3.61      inference('sup-', [status(thm)], ['135', '138'])).
% 3.32/3.61  thf('140', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('141', plain,
% 3.32/3.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.32/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.61  thf('142', plain,
% 3.32/3.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.32/3.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.32/3.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.32/3.61          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 3.32/3.61              = (k5_relat_1 @ X24 @ X27)))),
% 3.32/3.61      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 3.32/3.61  thf('143', plain,
% 3.32/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.61         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.32/3.61            = (k5_relat_1 @ sk_C @ X0))
% 3.32/3.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.32/3.61      inference('sup-', [status(thm)], ['141', '142'])).
% 3.32/3.61  thf('144', plain,
% 3.32/3.61      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.32/3.61         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.32/3.61      inference('sup-', [status(thm)], ['140', '143'])).
% 3.32/3.61  thf('145', plain,
% 3.32/3.61      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.32/3.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.32/3.61      inference('demod', [status(thm)], ['139', '144'])).
% 3.32/3.61  thf('146', plain,
% 3.32/3.61      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.32/3.61         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.32/3.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.32/3.61          | ((X30) = (X33))
% 3.32/3.61          | ~ (r2_relset_1 @ X31 @ X32 @ X30 @ X33))),
% 3.32/3.61      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.32/3.61  thf('147', plain,
% 3.32/3.61      (![X0 : $i]:
% 3.32/3.61         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 3.32/3.61          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 3.32/3.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.43/3.61      inference('sup-', [status(thm)], ['145', '146'])).
% 3.43/3.61  thf('148', plain,
% 3.43/3.61      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.43/3.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.43/3.61        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 3.43/3.61      inference('sup-', [status(thm)], ['134', '147'])).
% 3.43/3.61  thf('149', plain,
% 3.43/3.61      (![X34 : $i]:
% 3.43/3.61         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 3.43/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 3.43/3.61      inference('demod', [status(thm)], ['12', '13'])).
% 3.43/3.61  thf('150', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.43/3.61      inference('demod', [status(thm)], ['148', '149'])).
% 3.43/3.61  thf('151', plain, (![X8 : $i]: (v2_funct_1 @ (k6_partfun1 @ X8))),
% 3.43/3.61      inference('demod', [status(thm)], ['64', '65'])).
% 3.43/3.61  thf('152', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.43/3.61      inference('demod', [status(thm)], ['131', '150', '151'])).
% 3.43/3.61  thf('153', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.43/3.61      inference('split', [status(esa)], ['69'])).
% 3.43/3.61  thf('154', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.43/3.61      inference('sat_resolution*', [status(thm)], ['99', '100'])).
% 3.43/3.61  thf('155', plain, (~ (v2_funct_1 @ sk_C)),
% 3.43/3.61      inference('simpl_trail', [status(thm)], ['153', '154'])).
% 3.43/3.61  thf('156', plain, (((sk_A) = (k1_xboole_0))),
% 3.43/3.61      inference('clc', [status(thm)], ['152', '155'])).
% 3.43/3.61  thf('157', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.43/3.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.43/3.61  thf('158', plain, ($false),
% 3.43/3.61      inference('demod', [status(thm)], ['111', '156', '157'])).
% 3.43/3.61  
% 3.43/3.61  % SZS output end Refutation
% 3.43/3.61  
% 3.43/3.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
