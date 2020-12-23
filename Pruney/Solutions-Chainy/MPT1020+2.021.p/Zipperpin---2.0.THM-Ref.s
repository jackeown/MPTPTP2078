%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xa4xqxYdwt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:03 EST 2020

% Result     : Theorem 5.55s
% Output     : Refutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 297 expanded)
%              Number of leaves         :   41 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          : 1427 (5249 expanded)
%              Number of equality atoms :   70 ( 104 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('4',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X3 ) )
      = ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('13',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('15',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('22',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X0 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','27'])).

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

thf('29',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_funct_2 @ X34 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['43','46'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('53',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( X40
        = ( k2_funct_1 @ X43 ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40 ) @ ( k6_partfun1 @ X42 ) )
      | ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
       != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('67',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('68',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( X40
        = ( k2_funct_1 @ X43 ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40 ) @ ( k6_relat_1 @ X42 ) )
      | ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
       != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
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
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
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
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
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
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('76',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('82',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('83',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
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

thf('85',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v3_funct_2 @ X20 @ X21 @ X22 )
      | ( v2_funct_2 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('86',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('90',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_2 @ X24 @ X23 )
      | ( ( k2_relat_1 @ X24 )
        = X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('93',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('94',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('96',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('97',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['91','94','97'])).

thf('99',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['83','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v3_funct_2 @ X20 @ X21 @ X22 )
      | ( v2_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('102',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','77','78','79','80','99','105'])).

thf('107',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('109',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('112',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['109','112'])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['47','113','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xa4xqxYdwt
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.55/5.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.55/5.76  % Solved by: fo/fo7.sh
% 5.55/5.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.55/5.76  % done 5244 iterations in 5.308s
% 5.55/5.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.55/5.76  % SZS output start Refutation
% 5.55/5.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.55/5.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.55/5.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.55/5.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.55/5.76  thf(sk_B_type, type, sk_B: $i).
% 5.55/5.76  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 5.55/5.76  thf(sk_A_type, type, sk_A: $i).
% 5.55/5.76  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.55/5.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.55/5.76  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 5.55/5.76  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.55/5.76  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 5.55/5.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.55/5.76  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.55/5.76  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.55/5.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.55/5.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.55/5.76  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 5.55/5.76  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.55/5.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.55/5.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.55/5.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.55/5.76  thf(sk_C_type, type, sk_C: $i).
% 5.55/5.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.55/5.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.55/5.76  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.55/5.76  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.55/5.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.55/5.76  thf(t8_boole, axiom,
% 5.55/5.76    (![A:$i,B:$i]:
% 5.55/5.76     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 5.55/5.76  thf('1', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 5.55/5.76      inference('cnf', [status(esa)], [t8_boole])).
% 5.55/5.76  thf('2', plain,
% 5.55/5.76      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['0', '1'])).
% 5.55/5.76  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.55/5.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.55/5.76  thf(dt_k6_partfun1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( m1_subset_1 @
% 5.55/5.76         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 5.55/5.76       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 5.55/5.76  thf('4', plain,
% 5.55/5.76      (![X32 : $i]:
% 5.55/5.76         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 5.55/5.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.55/5.76  thf(redefinition_k6_partfun1, axiom,
% 5.55/5.76    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.55/5.76  thf('5', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('6', plain,
% 5.55/5.76      (![X32 : $i]:
% 5.55/5.76         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 5.55/5.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 5.55/5.76      inference('demod', [status(thm)], ['4', '5'])).
% 5.55/5.76  thf(cc4_relset_1, axiom,
% 5.55/5.76    (![A:$i,B:$i]:
% 5.55/5.76     ( ( v1_xboole_0 @ A ) =>
% 5.55/5.76       ( ![C:$i]:
% 5.55/5.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 5.55/5.76           ( v1_xboole_0 @ C ) ) ) ))).
% 5.55/5.76  thf('7', plain,
% 5.55/5.76      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.55/5.76         (~ (v1_xboole_0 @ X10)
% 5.55/5.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 5.55/5.76          | (v1_xboole_0 @ X11))),
% 5.55/5.76      inference('cnf', [status(esa)], [cc4_relset_1])).
% 5.55/5.76  thf('8', plain,
% 5.55/5.76      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['6', '7'])).
% 5.55/5.76  thf('9', plain,
% 5.55/5.76      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['0', '1'])).
% 5.55/5.76  thf('10', plain,
% 5.55/5.76      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k6_relat_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['8', '9'])).
% 5.55/5.76  thf('11', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['3', '10'])).
% 5.55/5.76  thf(t67_funct_1, axiom,
% 5.55/5.76    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 5.55/5.76  thf('12', plain,
% 5.55/5.76      (![X3 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X3)) = (k6_relat_1 @ X3))),
% 5.55/5.76      inference('cnf', [status(esa)], [t67_funct_1])).
% 5.55/5.76  thf('13', plain, (((k2_funct_1 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 5.55/5.76      inference('sup+', [status(thm)], ['11', '12'])).
% 5.55/5.76  thf('14', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['3', '10'])).
% 5.55/5.76  thf('15', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 5.55/5.76      inference('sup+', [status(thm)], ['13', '14'])).
% 5.55/5.76  thf('16', plain,
% 5.55/5.76      (![X0 : $i]: (((k1_xboole_0) = (k2_funct_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 5.55/5.76      inference('sup+', [status(thm)], ['2', '15'])).
% 5.55/5.76  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.55/5.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.55/5.76  thf('18', plain,
% 5.55/5.76      (![X0 : $i]: ((v1_xboole_0 @ (k2_funct_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 5.55/5.76      inference('sup+', [status(thm)], ['16', '17'])).
% 5.55/5.76  thf('19', plain,
% 5.55/5.76      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['0', '1'])).
% 5.55/5.76  thf('20', plain,
% 5.55/5.76      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['0', '1'])).
% 5.55/5.76  thf('21', plain,
% 5.55/5.76      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k6_relat_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['8', '9'])).
% 5.55/5.76  thf('22', plain,
% 5.55/5.76      (![X32 : $i]:
% 5.55/5.76         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 5.55/5.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 5.55/5.76      inference('demod', [status(thm)], ['4', '5'])).
% 5.55/5.76  thf('23', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 5.55/5.76          | ~ (v1_xboole_0 @ X0))),
% 5.55/5.76      inference('sup+', [status(thm)], ['21', '22'])).
% 5.55/5.76  thf(redefinition_r2_relset_1, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i,D:$i]:
% 5.55/5.76     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.55/5.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.55/5.76       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.55/5.76  thf('24', plain,
% 5.55/5.76      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 5.55/5.76         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 5.55/5.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 5.55/5.76          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 5.55/5.76          | ((X16) != (X19)))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.55/5.76  thf('25', plain,
% 5.55/5.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.55/5.76         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 5.55/5.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 5.55/5.76      inference('simplify', [status(thm)], ['24'])).
% 5.55/5.76  thf('26', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_xboole_0 @ X0)
% 5.55/5.76          | (r2_relset_1 @ X0 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['23', '25'])).
% 5.55/5.76  thf('27', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         ((r2_relset_1 @ X1 @ X1 @ X0 @ k1_xboole_0)
% 5.55/5.76          | ~ (v1_xboole_0 @ X0)
% 5.55/5.76          | ~ (v1_xboole_0 @ X1))),
% 5.55/5.76      inference('sup+', [status(thm)], ['20', '26'])).
% 5.55/5.76  thf('28', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.76         ((r2_relset_1 @ X2 @ X2 @ X1 @ X0)
% 5.55/5.76          | ~ (v1_xboole_0 @ X0)
% 5.55/5.76          | ~ (v1_xboole_0 @ X2)
% 5.55/5.76          | ~ (v1_xboole_0 @ X1))),
% 5.55/5.76      inference('sup+', [status(thm)], ['19', '27'])).
% 5.55/5.76  thf(t87_funct_2, conjecture,
% 5.55/5.76    (![A:$i,B:$i]:
% 5.55/5.76     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.55/5.76         ( v3_funct_2 @ B @ A @ A ) & 
% 5.55/5.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.55/5.76       ( ![C:$i]:
% 5.55/5.76         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 5.55/5.76             ( v3_funct_2 @ C @ A @ A ) & 
% 5.55/5.76             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.55/5.76           ( ( r2_relset_1 @
% 5.55/5.76               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 5.55/5.76               ( k6_partfun1 @ A ) ) =>
% 5.55/5.76             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 5.55/5.76  thf(zf_stmt_0, negated_conjecture,
% 5.55/5.76    (~( ![A:$i,B:$i]:
% 5.55/5.76        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.55/5.76            ( v3_funct_2 @ B @ A @ A ) & 
% 5.55/5.76            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.55/5.76          ( ![C:$i]:
% 5.55/5.76            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 5.55/5.76                ( v3_funct_2 @ C @ A @ A ) & 
% 5.55/5.76                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.55/5.76              ( ( r2_relset_1 @
% 5.55/5.76                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 5.55/5.76                  ( k6_partfun1 @ A ) ) =>
% 5.55/5.76                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 5.55/5.76    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 5.55/5.76  thf('29', plain,
% 5.55/5.76      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('30', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(redefinition_k2_funct_2, axiom,
% 5.55/5.76    (![A:$i,B:$i]:
% 5.55/5.76     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.55/5.76         ( v3_funct_2 @ B @ A @ A ) & 
% 5.55/5.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.55/5.76       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 5.55/5.76  thf('31', plain,
% 5.55/5.76      (![X33 : $i, X34 : $i]:
% 5.55/5.76         (((k2_funct_2 @ X34 @ X33) = (k2_funct_1 @ X33))
% 5.55/5.76          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 5.55/5.76          | ~ (v3_funct_2 @ X33 @ X34 @ X34)
% 5.55/5.76          | ~ (v1_funct_2 @ X33 @ X34 @ X34)
% 5.55/5.76          | ~ (v1_funct_1 @ X33))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 5.55/5.76  thf('32', plain,
% 5.55/5.76      ((~ (v1_funct_1 @ sk_B)
% 5.55/5.76        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.55/5.76        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.55/5.76        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['30', '31'])).
% 5.55/5.76  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('34', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('35', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('36', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 5.55/5.76      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 5.55/5.76  thf('37', plain,
% 5.55/5.76      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 5.55/5.76      inference('demod', [status(thm)], ['29', '36'])).
% 5.55/5.76  thf('38', plain,
% 5.55/5.76      ((~ (v1_xboole_0 @ sk_C)
% 5.55/5.76        | ~ (v1_xboole_0 @ sk_A)
% 5.55/5.76        | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['28', '37'])).
% 5.55/5.76  thf('39', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('40', plain,
% 5.55/5.76      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.55/5.76         (~ (v1_xboole_0 @ X10)
% 5.55/5.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 5.55/5.76          | (v1_xboole_0 @ X11))),
% 5.55/5.76      inference('cnf', [status(esa)], [cc4_relset_1])).
% 5.55/5.76  thf('41', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 5.55/5.76      inference('sup-', [status(thm)], ['39', '40'])).
% 5.55/5.76  thf('42', plain,
% 5.55/5.76      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 5.55/5.76      inference('clc', [status(thm)], ['38', '41'])).
% 5.55/5.76  thf('43', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_A))),
% 5.55/5.76      inference('sup-', [status(thm)], ['18', '42'])).
% 5.55/5.76  thf('44', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('45', plain,
% 5.55/5.76      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.55/5.76         (~ (v1_xboole_0 @ X10)
% 5.55/5.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 5.55/5.76          | (v1_xboole_0 @ X11))),
% 5.55/5.76      inference('cnf', [status(esa)], [cc4_relset_1])).
% 5.55/5.76  thf('46', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_A))),
% 5.55/5.76      inference('sup-', [status(thm)], ['44', '45'])).
% 5.55/5.76  thf('47', plain, (~ (v1_xboole_0 @ sk_A)),
% 5.55/5.76      inference('clc', [status(thm)], ['43', '46'])).
% 5.55/5.76  thf('48', plain,
% 5.55/5.76      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.55/5.76        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 5.55/5.76        (k6_partfun1 @ sk_A))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('49', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('50', plain,
% 5.55/5.76      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.55/5.76        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 5.55/5.76        (k6_relat_1 @ sk_A))),
% 5.55/5.76      inference('demod', [status(thm)], ['48', '49'])).
% 5.55/5.76  thf('51', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('52', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(dt_k1_partfun1, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.55/5.76     ( ( ( v1_funct_1 @ E ) & 
% 5.55/5.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.55/5.76         ( v1_funct_1 @ F ) & 
% 5.55/5.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.55/5.76       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.55/5.76         ( m1_subset_1 @
% 5.55/5.76           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.55/5.76           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.55/5.76  thf('53', plain,
% 5.55/5.76      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 5.55/5.76         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 5.55/5.76          | ~ (v1_funct_1 @ X25)
% 5.55/5.76          | ~ (v1_funct_1 @ X28)
% 5.55/5.76          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 5.55/5.76          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 5.55/5.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.55/5.76  thf('54', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 5.55/5.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.55/5.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.55/5.76          | ~ (v1_funct_1 @ X1)
% 5.55/5.76          | ~ (v1_funct_1 @ sk_B))),
% 5.55/5.76      inference('sup-', [status(thm)], ['52', '53'])).
% 5.55/5.76  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('56', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 5.55/5.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.55/5.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.55/5.76          | ~ (v1_funct_1 @ X1))),
% 5.55/5.76      inference('demod', [status(thm)], ['54', '55'])).
% 5.55/5.76  thf('57', plain,
% 5.55/5.76      ((~ (v1_funct_1 @ sk_C)
% 5.55/5.76        | (m1_subset_1 @ 
% 5.55/5.76           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 5.55/5.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['51', '56'])).
% 5.55/5.76  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('59', plain,
% 5.55/5.76      ((m1_subset_1 @ 
% 5.55/5.76        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 5.55/5.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('demod', [status(thm)], ['57', '58'])).
% 5.55/5.76  thf('60', plain,
% 5.55/5.76      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 5.55/5.76         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 5.55/5.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 5.55/5.76          | ((X16) = (X19))
% 5.55/5.76          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.55/5.76  thf('61', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.55/5.76             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 5.55/5.76          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 5.55/5.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['59', '60'])).
% 5.55/5.76  thf('62', plain,
% 5.55/5.76      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 5.55/5.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.55/5.76        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 5.55/5.76            = (k6_relat_1 @ sk_A)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['50', '61'])).
% 5.55/5.76  thf('63', plain,
% 5.55/5.76      (![X32 : $i]:
% 5.55/5.76         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 5.55/5.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 5.55/5.76      inference('demod', [status(thm)], ['4', '5'])).
% 5.55/5.76  thf('64', plain,
% 5.55/5.76      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 5.55/5.76         = (k6_relat_1 @ sk_A))),
% 5.55/5.76      inference('demod', [status(thm)], ['62', '63'])).
% 5.55/5.76  thf('65', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(t36_funct_2, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i]:
% 5.55/5.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.55/5.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.55/5.76       ( ![D:$i]:
% 5.55/5.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.55/5.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.55/5.76           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 5.55/5.76               ( r2_relset_1 @
% 5.55/5.76                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.55/5.76                 ( k6_partfun1 @ A ) ) & 
% 5.55/5.76               ( v2_funct_1 @ C ) ) =>
% 5.55/5.76             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.55/5.76               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 5.55/5.76  thf('66', plain,
% 5.55/5.76      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X40)
% 5.55/5.76          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 5.55/5.76          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 5.55/5.76          | ((X40) = (k2_funct_1 @ X43))
% 5.55/5.76          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 5.55/5.76               (k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40) @ 
% 5.55/5.76               (k6_partfun1 @ X42))
% 5.55/5.76          | ((X41) = (k1_xboole_0))
% 5.55/5.76          | ((X42) = (k1_xboole_0))
% 5.55/5.76          | ~ (v2_funct_1 @ X43)
% 5.55/5.76          | ((k2_relset_1 @ X42 @ X41 @ X43) != (X41))
% 5.55/5.76          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 5.55/5.76          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 5.55/5.76          | ~ (v1_funct_1 @ X43))),
% 5.55/5.76      inference('cnf', [status(esa)], [t36_funct_2])).
% 5.55/5.76  thf('67', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('68', plain,
% 5.55/5.76      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X40)
% 5.55/5.76          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 5.55/5.76          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 5.55/5.76          | ((X40) = (k2_funct_1 @ X43))
% 5.55/5.76          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 5.55/5.76               (k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40) @ 
% 5.55/5.76               (k6_relat_1 @ X42))
% 5.55/5.76          | ((X41) = (k1_xboole_0))
% 5.55/5.76          | ((X42) = (k1_xboole_0))
% 5.55/5.76          | ~ (v2_funct_1 @ X43)
% 5.55/5.76          | ((k2_relset_1 @ X42 @ X41 @ X43) != (X41))
% 5.55/5.76          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 5.55/5.76          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 5.55/5.76          | ~ (v1_funct_1 @ X43))),
% 5.55/5.76      inference('demod', [status(thm)], ['66', '67'])).
% 5.55/5.76  thf('69', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 5.55/5.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.55/5.76          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ((sk_A) = (k1_xboole_0))
% 5.55/5.76          | ((sk_A) = (k1_xboole_0))
% 5.55/5.76          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.55/5.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 5.55/5.76               (k6_relat_1 @ sk_A))
% 5.55/5.76          | ((sk_C) = (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 5.55/5.76          | ~ (v1_funct_1 @ sk_C))),
% 5.55/5.76      inference('sup-', [status(thm)], ['65', '68'])).
% 5.55/5.76  thf('70', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('72', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 5.55/5.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.55/5.76          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ((sk_A) = (k1_xboole_0))
% 5.55/5.76          | ((sk_A) = (k1_xboole_0))
% 5.55/5.76          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.55/5.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 5.55/5.76               (k6_relat_1 @ sk_A))
% 5.55/5.76          | ((sk_C) = (k2_funct_1 @ X0)))),
% 5.55/5.76      inference('demod', [status(thm)], ['69', '70', '71'])).
% 5.55/5.76  thf('73', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (((sk_C) = (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.55/5.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 5.55/5.76               (k6_relat_1 @ sk_A))
% 5.55/5.76          | ((sk_A) = (k1_xboole_0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 5.55/5.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.55/5.76          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 5.55/5.76          | ~ (v1_funct_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['72'])).
% 5.55/5.76  thf('74', plain,
% 5.55/5.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 5.55/5.76           (k6_relat_1 @ sk_A))
% 5.55/5.76        | ~ (v1_funct_1 @ sk_B)
% 5.55/5.76        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.55/5.76        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.55/5.76        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 5.55/5.76        | ~ (v2_funct_1 @ sk_B)
% 5.55/5.76        | ((sk_A) = (k1_xboole_0))
% 5.55/5.76        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['64', '73'])).
% 5.55/5.76  thf('75', plain,
% 5.55/5.76      (![X32 : $i]:
% 5.55/5.76         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 5.55/5.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 5.55/5.76      inference('demod', [status(thm)], ['4', '5'])).
% 5.55/5.76  thf('76', plain,
% 5.55/5.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.55/5.76         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 5.55/5.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 5.55/5.76      inference('simplify', [status(thm)], ['24'])).
% 5.55/5.76  thf('77', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['75', '76'])).
% 5.55/5.76  thf('78', plain, ((v1_funct_1 @ sk_B)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('79', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('80', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('81', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(redefinition_k2_relset_1, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i]:
% 5.55/5.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.55/5.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.55/5.76  thf('82', plain,
% 5.55/5.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.55/5.76         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 5.55/5.76          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.55/5.76  thf('83', plain,
% 5.55/5.76      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 5.55/5.76      inference('sup-', [status(thm)], ['81', '82'])).
% 5.55/5.76  thf('84', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(cc2_funct_2, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i]:
% 5.55/5.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.55/5.76       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 5.55/5.76         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 5.55/5.76  thf('85', plain,
% 5.55/5.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X20)
% 5.55/5.76          | ~ (v3_funct_2 @ X20 @ X21 @ X22)
% 5.55/5.76          | (v2_funct_2 @ X20 @ X22)
% 5.55/5.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 5.55/5.76      inference('cnf', [status(esa)], [cc2_funct_2])).
% 5.55/5.76  thf('86', plain,
% 5.55/5.76      (((v2_funct_2 @ sk_B @ sk_A)
% 5.55/5.76        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_B))),
% 5.55/5.76      inference('sup-', [status(thm)], ['84', '85'])).
% 5.55/5.76  thf('87', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('88', plain, ((v1_funct_1 @ sk_B)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('89', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87', '88'])).
% 5.55/5.76  thf(d3_funct_2, axiom,
% 5.55/5.76    (![A:$i,B:$i]:
% 5.55/5.76     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 5.55/5.76       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 5.55/5.76  thf('90', plain,
% 5.55/5.76      (![X23 : $i, X24 : $i]:
% 5.55/5.76         (~ (v2_funct_2 @ X24 @ X23)
% 5.55/5.76          | ((k2_relat_1 @ X24) = (X23))
% 5.55/5.76          | ~ (v5_relat_1 @ X24 @ X23)
% 5.55/5.76          | ~ (v1_relat_1 @ X24))),
% 5.55/5.76      inference('cnf', [status(esa)], [d3_funct_2])).
% 5.55/5.76  thf('91', plain,
% 5.55/5.76      ((~ (v1_relat_1 @ sk_B)
% 5.55/5.76        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 5.55/5.76        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['89', '90'])).
% 5.55/5.76  thf('92', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(cc1_relset_1, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i]:
% 5.55/5.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.55/5.76       ( v1_relat_1 @ C ) ))).
% 5.55/5.76  thf('93', plain,
% 5.55/5.76      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.55/5.76         ((v1_relat_1 @ X4)
% 5.55/5.76          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 5.55/5.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.55/5.76  thf('94', plain, ((v1_relat_1 @ sk_B)),
% 5.55/5.76      inference('sup-', [status(thm)], ['92', '93'])).
% 5.55/5.76  thf('95', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(cc2_relset_1, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i]:
% 5.55/5.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.55/5.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.55/5.76  thf('96', plain,
% 5.55/5.76      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.55/5.76         ((v5_relat_1 @ X7 @ X9)
% 5.55/5.76          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 5.55/5.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.55/5.76  thf('97', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 5.55/5.76      inference('sup-', [status(thm)], ['95', '96'])).
% 5.55/5.76  thf('98', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 5.55/5.76      inference('demod', [status(thm)], ['91', '94', '97'])).
% 5.55/5.76  thf('99', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 5.55/5.76      inference('demod', [status(thm)], ['83', '98'])).
% 5.55/5.76  thf('100', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('101', plain,
% 5.55/5.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X20)
% 5.55/5.76          | ~ (v3_funct_2 @ X20 @ X21 @ X22)
% 5.55/5.76          | (v2_funct_1 @ X20)
% 5.55/5.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 5.55/5.76      inference('cnf', [status(esa)], [cc2_funct_2])).
% 5.55/5.76  thf('102', plain,
% 5.55/5.76      (((v2_funct_1 @ sk_B)
% 5.55/5.76        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_B))),
% 5.55/5.76      inference('sup-', [status(thm)], ['100', '101'])).
% 5.55/5.76  thf('103', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('104', plain, ((v1_funct_1 @ sk_B)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('105', plain, ((v2_funct_1 @ sk_B)),
% 5.55/5.76      inference('demod', [status(thm)], ['102', '103', '104'])).
% 5.55/5.76  thf('106', plain,
% 5.55/5.76      ((((sk_A) != (sk_A))
% 5.55/5.76        | ((sk_A) = (k1_xboole_0))
% 5.55/5.76        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 5.55/5.76      inference('demod', [status(thm)],
% 5.55/5.76                ['74', '77', '78', '79', '80', '99', '105'])).
% 5.55/5.76  thf('107', plain,
% 5.55/5.76      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 5.55/5.76      inference('simplify', [status(thm)], ['106'])).
% 5.55/5.76  thf('108', plain,
% 5.55/5.76      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 5.55/5.76      inference('demod', [status(thm)], ['29', '36'])).
% 5.55/5.76  thf('109', plain,
% 5.55/5.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['107', '108'])).
% 5.55/5.76  thf('110', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('111', plain,
% 5.55/5.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.55/5.76         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 5.55/5.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 5.55/5.76      inference('simplify', [status(thm)], ['24'])).
% 5.55/5.76  thf('112', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 5.55/5.76      inference('sup-', [status(thm)], ['110', '111'])).
% 5.55/5.76  thf('113', plain, (((sk_A) = (k1_xboole_0))),
% 5.55/5.76      inference('demod', [status(thm)], ['109', '112'])).
% 5.55/5.76  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.55/5.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.55/5.76  thf('115', plain, ($false),
% 5.55/5.76      inference('demod', [status(thm)], ['47', '113', '114'])).
% 5.55/5.76  
% 5.55/5.76  % SZS output end Refutation
% 5.55/5.76  
% 5.55/5.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
