%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dkE8w9yJi5

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:07 EST 2020

% Result     : Theorem 3.99s
% Output     : Refutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 319 expanded)
%              Number of leaves         :   46 ( 114 expanded)
%              Depth                    :   16
%              Number of atoms          : 1206 (4782 expanded)
%              Number of equality atoms :   43 (  87 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('1',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['1','2'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('5',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

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

thf('9',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('14',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45 ) @ ( k6_partfun1 @ X43 ) )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['19','22','23','24','25'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('27',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('28',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('35',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('37',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('38',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['33','36','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( v5_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('43',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ X34 )
       != X33 )
      | ( v2_funct_2 @ X34 @ X33 )
      | ~ ( v5_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('44',plain,(
    ! [X34: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ~ ( v5_relat_1 @ X34 @ ( k2_relat_1 @ X34 ) )
      | ( v2_funct_2 @ X34 @ ( k2_relat_1 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['26','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('53',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('55',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['11','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('58',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('63',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('70',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('74',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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

thf('76',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X49 @ X47 @ X47 @ X48 @ X50 @ X46 ) )
      | ( v2_funct_1 @ X50 )
      | ( X48 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X47 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('88',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('89',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['87','88'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['86','89'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('91',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('92',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['1','2'])).

thf('97',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('98',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['1','2'])).

thf('100',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('101',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['95','98','101'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('103',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('104',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['59','90','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['56','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dkE8w9yJi5
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:36:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.99/4.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.99/4.18  % Solved by: fo/fo7.sh
% 3.99/4.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.99/4.18  % done 5100 iterations in 3.716s
% 3.99/4.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.99/4.18  % SZS output start Refutation
% 3.99/4.18  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.99/4.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.99/4.18  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.99/4.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.99/4.18  thf(sk_B_type, type, sk_B: $i > $i).
% 3.99/4.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.99/4.18  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.99/4.18  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.99/4.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.99/4.18  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.99/4.18  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.99/4.18  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.99/4.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.99/4.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.99/4.18  thf(sk_A_type, type, sk_A: $i).
% 3.99/4.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.99/4.18  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.99/4.18  thf(sk_D_type, type, sk_D: $i).
% 3.99/4.18  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.99/4.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.99/4.18  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.99/4.18  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.99/4.18  thf(sk_C_type, type, sk_C: $i).
% 3.99/4.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.99/4.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.99/4.18  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.99/4.18  thf(l13_xboole_0, axiom,
% 3.99/4.18    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.99/4.18  thf('0', plain,
% 3.99/4.18      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 3.99/4.18      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.99/4.18  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.99/4.18  thf('1', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.99/4.18      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.99/4.18  thf(redefinition_k6_partfun1, axiom,
% 3.99/4.18    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.99/4.18  thf('2', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 3.99/4.18      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.18  thf('3', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.99/4.18      inference('demod', [status(thm)], ['1', '2'])).
% 3.99/4.18  thf(fc4_funct_1, axiom,
% 3.99/4.18    (![A:$i]:
% 3.99/4.18     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.99/4.18       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.99/4.18  thf('4', plain, (![X13 : $i]: (v2_funct_1 @ (k6_relat_1 @ X13))),
% 3.99/4.18      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.99/4.18  thf('5', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 3.99/4.18      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.18  thf('6', plain, (![X13 : $i]: (v2_funct_1 @ (k6_partfun1 @ X13))),
% 3.99/4.18      inference('demod', [status(thm)], ['4', '5'])).
% 3.99/4.18  thf('7', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.99/4.18      inference('sup+', [status(thm)], ['3', '6'])).
% 3.99/4.18  thf('8', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.99/4.18      inference('sup+', [status(thm)], ['0', '7'])).
% 3.99/4.18  thf(t29_funct_2, conjecture,
% 3.99/4.18    (![A:$i,B:$i,C:$i]:
% 3.99/4.18     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.99/4.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.99/4.18       ( ![D:$i]:
% 3.99/4.18         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.99/4.18             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.99/4.18           ( ( r2_relset_1 @
% 3.99/4.18               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.99/4.18               ( k6_partfun1 @ A ) ) =>
% 3.99/4.18             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.99/4.18  thf(zf_stmt_0, negated_conjecture,
% 3.99/4.18    (~( ![A:$i,B:$i,C:$i]:
% 3.99/4.18        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.99/4.18            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.99/4.18          ( ![D:$i]:
% 3.99/4.18            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.99/4.18                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.99/4.18              ( ( r2_relset_1 @
% 3.99/4.18                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.99/4.18                  ( k6_partfun1 @ A ) ) =>
% 3.99/4.18                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.99/4.18    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.99/4.18  thf('9', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('10', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.99/4.18      inference('split', [status(esa)], ['9'])).
% 3.99/4.18  thf('11', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.99/4.18      inference('sup-', [status(thm)], ['8', '10'])).
% 3.99/4.18  thf('12', plain,
% 3.99/4.18      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.99/4.18        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.99/4.18        (k6_partfun1 @ sk_A))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('13', plain,
% 3.99/4.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf(t24_funct_2, axiom,
% 3.99/4.18    (![A:$i,B:$i,C:$i]:
% 3.99/4.18     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.99/4.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.99/4.18       ( ![D:$i]:
% 3.99/4.18         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.99/4.18             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.99/4.18           ( ( r2_relset_1 @
% 3.99/4.18               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.99/4.18               ( k6_partfun1 @ B ) ) =>
% 3.99/4.18             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.99/4.18  thf('14', plain,
% 3.99/4.18      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 3.99/4.18         (~ (v1_funct_1 @ X42)
% 3.99/4.18          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 3.99/4.18          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.99/4.18          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 3.99/4.18               (k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45) @ 
% 3.99/4.18               (k6_partfun1 @ X43))
% 3.99/4.18          | ((k2_relset_1 @ X44 @ X43 @ X45) = (X43))
% 3.99/4.18          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 3.99/4.18          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 3.99/4.18          | ~ (v1_funct_1 @ X45))),
% 3.99/4.18      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.99/4.18  thf('15', plain,
% 3.99/4.18      (![X0 : $i]:
% 3.99/4.18         (~ (v1_funct_1 @ X0)
% 3.99/4.18          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.99/4.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.99/4.18          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.99/4.18          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.99/4.18               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.99/4.18               (k6_partfun1 @ sk_A))
% 3.99/4.18          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.99/4.18          | ~ (v1_funct_1 @ sk_C))),
% 3.99/4.18      inference('sup-', [status(thm)], ['13', '14'])).
% 3.99/4.18  thf('16', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('18', plain,
% 3.99/4.18      (![X0 : $i]:
% 3.99/4.18         (~ (v1_funct_1 @ X0)
% 3.99/4.18          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.99/4.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.99/4.18          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.99/4.18          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.99/4.18               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.99/4.18               (k6_partfun1 @ sk_A)))),
% 3.99/4.18      inference('demod', [status(thm)], ['15', '16', '17'])).
% 3.99/4.18  thf('19', plain,
% 3.99/4.18      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 3.99/4.18        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.99/4.18        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.99/4.18        | ~ (v1_funct_1 @ sk_D))),
% 3.99/4.18      inference('sup-', [status(thm)], ['12', '18'])).
% 3.99/4.18  thf('20', plain,
% 3.99/4.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf(redefinition_k2_relset_1, axiom,
% 3.99/4.18    (![A:$i,B:$i,C:$i]:
% 3.99/4.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.99/4.18       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.99/4.18  thf('21', plain,
% 3.99/4.18      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.99/4.18         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 3.99/4.18          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.99/4.18      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.99/4.18  thf('22', plain,
% 3.99/4.18      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.99/4.18      inference('sup-', [status(thm)], ['20', '21'])).
% 3.99/4.18  thf('23', plain,
% 3.99/4.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('26', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.99/4.18      inference('demod', [status(thm)], ['19', '22', '23', '24', '25'])).
% 3.99/4.18  thf(t29_relset_1, axiom,
% 3.99/4.18    (![A:$i]:
% 3.99/4.18     ( m1_subset_1 @
% 3.99/4.18       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.99/4.18  thf('27', plain,
% 3.99/4.18      (![X32 : $i]:
% 3.99/4.18         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 3.99/4.18          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 3.99/4.18      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.99/4.18  thf('28', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 3.99/4.18      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.18  thf('29', plain,
% 3.99/4.18      (![X32 : $i]:
% 3.99/4.18         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 3.99/4.18          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 3.99/4.18      inference('demod', [status(thm)], ['27', '28'])).
% 3.99/4.18  thf(cc2_relset_1, axiom,
% 3.99/4.18    (![A:$i,B:$i,C:$i]:
% 3.99/4.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.99/4.18       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.99/4.18  thf('30', plain,
% 3.99/4.18      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.99/4.18         ((v5_relat_1 @ X19 @ X21)
% 3.99/4.18          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.99/4.18      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.99/4.18  thf('31', plain, (![X0 : $i]: (v5_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 3.99/4.18      inference('sup-', [status(thm)], ['29', '30'])).
% 3.99/4.18  thf(d19_relat_1, axiom,
% 3.99/4.18    (![A:$i,B:$i]:
% 3.99/4.18     ( ( v1_relat_1 @ B ) =>
% 3.99/4.18       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.99/4.18  thf('32', plain,
% 3.99/4.18      (![X8 : $i, X9 : $i]:
% 3.99/4.18         (~ (v5_relat_1 @ X8 @ X9)
% 3.99/4.18          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 3.99/4.18          | ~ (v1_relat_1 @ X8))),
% 3.99/4.18      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.99/4.18  thf('33', plain,
% 3.99/4.18      (![X0 : $i]:
% 3.99/4.18         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 3.99/4.18          | (r1_tarski @ (k2_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 3.99/4.18      inference('sup-', [status(thm)], ['31', '32'])).
% 3.99/4.18  thf('34', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 3.99/4.18      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.99/4.18  thf('35', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 3.99/4.18      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.18  thf('36', plain, (![X12 : $i]: (v1_relat_1 @ (k6_partfun1 @ X12))),
% 3.99/4.18      inference('demod', [status(thm)], ['34', '35'])).
% 3.99/4.18  thf(t71_relat_1, axiom,
% 3.99/4.18    (![A:$i]:
% 3.99/4.18     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.99/4.18       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.99/4.18  thf('37', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 3.99/4.18      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.99/4.18  thf('38', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 3.99/4.18      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.18  thf('39', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X11)) = (X11))),
% 3.99/4.18      inference('demod', [status(thm)], ['37', '38'])).
% 3.99/4.18  thf('40', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.99/4.18      inference('demod', [status(thm)], ['33', '36', '39'])).
% 3.99/4.18  thf('41', plain,
% 3.99/4.18      (![X8 : $i, X9 : $i]:
% 3.99/4.18         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 3.99/4.18          | (v5_relat_1 @ X8 @ X9)
% 3.99/4.18          | ~ (v1_relat_1 @ X8))),
% 3.99/4.18      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.99/4.18  thf('42', plain,
% 3.99/4.18      (![X0 : $i]:
% 3.99/4.18         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.99/4.18      inference('sup-', [status(thm)], ['40', '41'])).
% 3.99/4.18  thf(d3_funct_2, axiom,
% 3.99/4.18    (![A:$i,B:$i]:
% 3.99/4.18     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.99/4.18       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.99/4.18  thf('43', plain,
% 3.99/4.18      (![X33 : $i, X34 : $i]:
% 3.99/4.18         (((k2_relat_1 @ X34) != (X33))
% 3.99/4.18          | (v2_funct_2 @ X34 @ X33)
% 3.99/4.18          | ~ (v5_relat_1 @ X34 @ X33)
% 3.99/4.18          | ~ (v1_relat_1 @ X34))),
% 3.99/4.18      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.99/4.18  thf('44', plain,
% 3.99/4.18      (![X34 : $i]:
% 3.99/4.18         (~ (v1_relat_1 @ X34)
% 3.99/4.18          | ~ (v5_relat_1 @ X34 @ (k2_relat_1 @ X34))
% 3.99/4.18          | (v2_funct_2 @ X34 @ (k2_relat_1 @ X34)))),
% 3.99/4.18      inference('simplify', [status(thm)], ['43'])).
% 3.99/4.18  thf('45', plain,
% 3.99/4.18      (![X0 : $i]:
% 3.99/4.18         (~ (v1_relat_1 @ X0)
% 3.99/4.18          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 3.99/4.18          | ~ (v1_relat_1 @ X0))),
% 3.99/4.18      inference('sup-', [status(thm)], ['42', '44'])).
% 3.99/4.18  thf('46', plain,
% 3.99/4.18      (![X0 : $i]:
% 3.99/4.18         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.99/4.18      inference('simplify', [status(thm)], ['45'])).
% 3.99/4.18  thf('47', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 3.99/4.18      inference('sup+', [status(thm)], ['26', '46'])).
% 3.99/4.18  thf('48', plain,
% 3.99/4.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf(cc1_relset_1, axiom,
% 3.99/4.18    (![A:$i,B:$i,C:$i]:
% 3.99/4.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.99/4.18       ( v1_relat_1 @ C ) ))).
% 3.99/4.18  thf('49', plain,
% 3.99/4.18      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.99/4.18         ((v1_relat_1 @ X16)
% 3.99/4.18          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.99/4.18      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.99/4.18  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 3.99/4.18      inference('sup-', [status(thm)], ['48', '49'])).
% 3.99/4.18  thf('51', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.99/4.18      inference('demod', [status(thm)], ['47', '50'])).
% 3.99/4.18  thf('52', plain,
% 3.99/4.18      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.99/4.18      inference('split', [status(esa)], ['9'])).
% 3.99/4.18  thf('53', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.99/4.18      inference('sup-', [status(thm)], ['51', '52'])).
% 3.99/4.18  thf('54', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.99/4.18      inference('split', [status(esa)], ['9'])).
% 3.99/4.18  thf('55', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.99/4.18      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 3.99/4.18  thf('56', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.99/4.18      inference('simpl_trail', [status(thm)], ['11', '55'])).
% 3.99/4.18  thf('57', plain,
% 3.99/4.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf(cc3_relset_1, axiom,
% 3.99/4.18    (![A:$i,B:$i]:
% 3.99/4.18     ( ( v1_xboole_0 @ A ) =>
% 3.99/4.18       ( ![C:$i]:
% 3.99/4.18         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.99/4.18           ( v1_xboole_0 @ C ) ) ) ))).
% 3.99/4.18  thf('58', plain,
% 3.99/4.18      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.99/4.18         (~ (v1_xboole_0 @ X22)
% 3.99/4.18          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 3.99/4.18          | (v1_xboole_0 @ X23))),
% 3.99/4.18      inference('cnf', [status(esa)], [cc3_relset_1])).
% 3.99/4.18  thf('59', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 3.99/4.18      inference('sup-', [status(thm)], ['57', '58'])).
% 3.99/4.18  thf('60', plain,
% 3.99/4.18      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.99/4.18        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.99/4.18        (k6_partfun1 @ sk_A))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('61', plain,
% 3.99/4.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('62', plain,
% 3.99/4.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf(dt_k1_partfun1, axiom,
% 3.99/4.18    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.99/4.18     ( ( ( v1_funct_1 @ E ) & 
% 3.99/4.18         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.99/4.18         ( v1_funct_1 @ F ) & 
% 3.99/4.18         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.99/4.18       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.99/4.18         ( m1_subset_1 @
% 3.99/4.18           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.99/4.18           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.99/4.18  thf('63', plain,
% 3.99/4.18      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 3.99/4.18         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.99/4.18          | ~ (v1_funct_1 @ X35)
% 3.99/4.18          | ~ (v1_funct_1 @ X38)
% 3.99/4.18          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 3.99/4.18          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 3.99/4.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 3.99/4.18      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.99/4.18  thf('64', plain,
% 3.99/4.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.99/4.18         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 3.99/4.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.99/4.18          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.99/4.18          | ~ (v1_funct_1 @ X1)
% 3.99/4.18          | ~ (v1_funct_1 @ sk_C))),
% 3.99/4.18      inference('sup-', [status(thm)], ['62', '63'])).
% 3.99/4.18  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('66', plain,
% 3.99/4.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.99/4.18         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 3.99/4.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.99/4.18          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.99/4.18          | ~ (v1_funct_1 @ X1))),
% 3.99/4.18      inference('demod', [status(thm)], ['64', '65'])).
% 3.99/4.18  thf('67', plain,
% 3.99/4.18      ((~ (v1_funct_1 @ sk_D)
% 3.99/4.18        | (m1_subset_1 @ 
% 3.99/4.18           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.99/4.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.99/4.18      inference('sup-', [status(thm)], ['61', '66'])).
% 3.99/4.18  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('69', plain,
% 3.99/4.18      ((m1_subset_1 @ 
% 3.99/4.18        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.99/4.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.99/4.18      inference('demod', [status(thm)], ['67', '68'])).
% 3.99/4.18  thf(redefinition_r2_relset_1, axiom,
% 3.99/4.18    (![A:$i,B:$i,C:$i,D:$i]:
% 3.99/4.18     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.99/4.18         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.99/4.18       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.99/4.18  thf('70', plain,
% 3.99/4.18      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.99/4.18         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.99/4.18          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.99/4.18          | ((X28) = (X31))
% 3.99/4.18          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 3.99/4.18      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.99/4.18  thf('71', plain,
% 3.99/4.18      (![X0 : $i]:
% 3.99/4.18         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.99/4.18             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 3.99/4.18          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 3.99/4.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.99/4.18      inference('sup-', [status(thm)], ['69', '70'])).
% 3.99/4.18  thf('72', plain,
% 3.99/4.18      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.99/4.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.99/4.18        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.99/4.18            = (k6_partfun1 @ sk_A)))),
% 3.99/4.18      inference('sup-', [status(thm)], ['60', '71'])).
% 3.99/4.18  thf('73', plain,
% 3.99/4.18      (![X32 : $i]:
% 3.99/4.18         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 3.99/4.18          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 3.99/4.18      inference('demod', [status(thm)], ['27', '28'])).
% 3.99/4.18  thf('74', plain,
% 3.99/4.18      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.99/4.18         = (k6_partfun1 @ sk_A))),
% 3.99/4.18      inference('demod', [status(thm)], ['72', '73'])).
% 3.99/4.18  thf('75', plain,
% 3.99/4.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf(t26_funct_2, axiom,
% 3.99/4.18    (![A:$i,B:$i,C:$i,D:$i]:
% 3.99/4.18     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.99/4.18         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.99/4.18       ( ![E:$i]:
% 3.99/4.18         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.99/4.18             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.99/4.18           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.99/4.18             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.99/4.18               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.99/4.18  thf('76', plain,
% 3.99/4.18      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 3.99/4.18         (~ (v1_funct_1 @ X46)
% 3.99/4.18          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 3.99/4.18          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 3.99/4.18          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X47 @ X47 @ X48 @ X50 @ X46))
% 3.99/4.18          | (v2_funct_1 @ X50)
% 3.99/4.18          | ((X48) = (k1_xboole_0))
% 3.99/4.18          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 3.99/4.18          | ~ (v1_funct_2 @ X50 @ X49 @ X47)
% 3.99/4.18          | ~ (v1_funct_1 @ X50))),
% 3.99/4.18      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.99/4.18  thf('77', plain,
% 3.99/4.18      (![X0 : $i, X1 : $i]:
% 3.99/4.18         (~ (v1_funct_1 @ X0)
% 3.99/4.18          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.99/4.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.99/4.18          | ((sk_A) = (k1_xboole_0))
% 3.99/4.18          | (v2_funct_1 @ X0)
% 3.99/4.18          | ~ (v2_funct_1 @ 
% 3.99/4.18               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 3.99/4.18          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.99/4.18          | ~ (v1_funct_1 @ sk_D))),
% 3.99/4.18      inference('sup-', [status(thm)], ['75', '76'])).
% 3.99/4.18  thf('78', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('79', plain, ((v1_funct_1 @ sk_D)),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('80', plain,
% 3.99/4.18      (![X0 : $i, X1 : $i]:
% 3.99/4.18         (~ (v1_funct_1 @ X0)
% 3.99/4.18          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.99/4.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.99/4.18          | ((sk_A) = (k1_xboole_0))
% 3.99/4.18          | (v2_funct_1 @ X0)
% 3.99/4.18          | ~ (v2_funct_1 @ 
% 3.99/4.18               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 3.99/4.18      inference('demod', [status(thm)], ['77', '78', '79'])).
% 3.99/4.18  thf('81', plain,
% 3.99/4.18      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.99/4.18        | (v2_funct_1 @ sk_C)
% 3.99/4.18        | ((sk_A) = (k1_xboole_0))
% 3.99/4.18        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 3.99/4.18        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.99/4.18        | ~ (v1_funct_1 @ sk_C))),
% 3.99/4.18      inference('sup-', [status(thm)], ['74', '80'])).
% 3.99/4.18  thf('82', plain, (![X13 : $i]: (v2_funct_1 @ (k6_partfun1 @ X13))),
% 3.99/4.18      inference('demod', [status(thm)], ['4', '5'])).
% 3.99/4.18  thf('83', plain,
% 3.99/4.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('84', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.18  thf('86', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.99/4.18      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 3.99/4.18  thf('87', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.99/4.18      inference('split', [status(esa)], ['9'])).
% 3.99/4.18  thf('88', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.99/4.18      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 3.99/4.18  thf('89', plain, (~ (v2_funct_1 @ sk_C)),
% 3.99/4.18      inference('simpl_trail', [status(thm)], ['87', '88'])).
% 3.99/4.18  thf('90', plain, (((sk_A) = (k1_xboole_0))),
% 3.99/4.18      inference('clc', [status(thm)], ['86', '89'])).
% 3.99/4.18  thf(t4_subset_1, axiom,
% 3.99/4.18    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.99/4.18  thf('91', plain,
% 3.99/4.18      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.99/4.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.99/4.18  thf('92', plain,
% 3.99/4.18      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.99/4.18         ((v5_relat_1 @ X19 @ X21)
% 3.99/4.18          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.99/4.18      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.99/4.18  thf('93', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 3.99/4.18      inference('sup-', [status(thm)], ['91', '92'])).
% 3.99/4.18  thf('94', plain,
% 3.99/4.18      (![X8 : $i, X9 : $i]:
% 3.99/4.18         (~ (v5_relat_1 @ X8 @ X9)
% 3.99/4.18          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 3.99/4.18          | ~ (v1_relat_1 @ X8))),
% 3.99/4.18      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.99/4.18  thf('95', plain,
% 3.99/4.18      (![X0 : $i]:
% 3.99/4.18         (~ (v1_relat_1 @ k1_xboole_0)
% 3.99/4.18          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 3.99/4.18      inference('sup-', [status(thm)], ['93', '94'])).
% 3.99/4.18  thf('96', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.99/4.18      inference('demod', [status(thm)], ['1', '2'])).
% 3.99/4.18  thf('97', plain, (![X12 : $i]: (v1_relat_1 @ (k6_partfun1 @ X12))),
% 3.99/4.18      inference('demod', [status(thm)], ['34', '35'])).
% 3.99/4.18  thf('98', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.99/4.18      inference('sup+', [status(thm)], ['96', '97'])).
% 3.99/4.18  thf('99', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.99/4.18      inference('demod', [status(thm)], ['1', '2'])).
% 3.99/4.18  thf('100', plain,
% 3.99/4.18      (![X11 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X11)) = (X11))),
% 3.99/4.18      inference('demod', [status(thm)], ['37', '38'])).
% 3.99/4.18  thf('101', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.99/4.18      inference('sup+', [status(thm)], ['99', '100'])).
% 3.99/4.18  thf('102', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.99/4.18      inference('demod', [status(thm)], ['95', '98', '101'])).
% 3.99/4.18  thf(d1_xboole_0, axiom,
% 3.99/4.18    (![A:$i]:
% 3.99/4.18     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.99/4.18  thf('103', plain,
% 3.99/4.18      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.99/4.18      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.99/4.18  thf(t7_ordinal1, axiom,
% 3.99/4.18    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.99/4.18  thf('104', plain,
% 3.99/4.18      (![X14 : $i, X15 : $i]:
% 3.99/4.18         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 3.99/4.18      inference('cnf', [status(esa)], [t7_ordinal1])).
% 3.99/4.18  thf('105', plain,
% 3.99/4.18      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 3.99/4.18      inference('sup-', [status(thm)], ['103', '104'])).
% 3.99/4.18  thf('106', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.99/4.18      inference('sup-', [status(thm)], ['102', '105'])).
% 3.99/4.18  thf('107', plain, ((v1_xboole_0 @ sk_C)),
% 3.99/4.18      inference('demod', [status(thm)], ['59', '90', '106'])).
% 3.99/4.18  thf('108', plain, ($false), inference('demod', [status(thm)], ['56', '107'])).
% 3.99/4.18  
% 3.99/4.18  % SZS output end Refutation
% 3.99/4.18  
% 3.99/4.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
