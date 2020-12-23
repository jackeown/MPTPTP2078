%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i786azOAkj

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:06 EST 2020

% Result     : Theorem 3.51s
% Output     : Refutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 273 expanded)
%              Number of leaves         :   44 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          : 1144 (4557 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
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

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('8',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X1
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('18',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['20'])).

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

thf('22',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('26',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( r2_relset_1 @ X46 @ X46 @ ( k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48 ) @ ( k6_partfun1 @ X46 ) )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
        = X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['31','34','35','36','37'])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( v5_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k2_relat_1 @ X37 )
       != X36 )
      | ( v2_funct_2 @ X37 @ X36 )
      | ~ ( v5_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('44',plain,(
    ! [X37: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v5_relat_1 @ X37 @ ( k2_relat_1 @ X37 ) )
      | ( v2_funct_2 @ X37 @ ( k2_relat_1 @ X37 ) ) ) ),
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
    inference('sup+',[status(thm)],['38','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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
    inference(split,[status(esa)],['22'])).

thf('53',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('55',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['23','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('64',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('71',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( X31 = X34 )
      | ~ ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','72'])).

thf('74',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('75',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
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

thf('77',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X52 @ X50 @ X50 @ X51 @ X53 @ X49 ) )
      | ( v2_funct_1 @ X53 )
      | ( X51 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X50 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('84',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['23','55'])).

thf('89',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['87','88'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['60','89','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['57','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i786azOAkj
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.51/3.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.51/3.71  % Solved by: fo/fo7.sh
% 3.51/3.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.51/3.71  % done 3216 iterations in 3.225s
% 3.51/3.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.51/3.71  % SZS output start Refutation
% 3.51/3.71  thf(sk_B_type, type, sk_B: $i).
% 3.51/3.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.51/3.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.51/3.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.51/3.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.51/3.71  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.51/3.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.51/3.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.51/3.71  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.51/3.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.51/3.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.51/3.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.51/3.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.51/3.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.51/3.71  thf(sk_A_type, type, sk_A: $i).
% 3.51/3.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.51/3.71  thf(sk_D_type, type, sk_D: $i).
% 3.51/3.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.51/3.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.51/3.71  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.51/3.71  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.51/3.71  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 3.51/3.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.51/3.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.51/3.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.51/3.71  thf(t29_relset_1, axiom,
% 3.51/3.71    (![A:$i]:
% 3.51/3.71     ( m1_subset_1 @
% 3.51/3.71       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.51/3.71  thf('0', plain,
% 3.51/3.71      (![X35 : $i]:
% 3.51/3.71         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 3.51/3.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 3.51/3.71      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.51/3.71  thf(redefinition_k6_partfun1, axiom,
% 3.51/3.71    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.51/3.71  thf('1', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 3.51/3.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.51/3.71  thf('2', plain,
% 3.51/3.71      (![X35 : $i]:
% 3.51/3.71         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 3.51/3.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 3.51/3.71      inference('demod', [status(thm)], ['0', '1'])).
% 3.51/3.71  thf(cc3_relset_1, axiom,
% 3.51/3.71    (![A:$i,B:$i]:
% 3.51/3.71     ( ( v1_xboole_0 @ A ) =>
% 3.51/3.71       ( ![C:$i]:
% 3.51/3.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.51/3.71           ( v1_xboole_0 @ C ) ) ) ))).
% 3.51/3.71  thf('3', plain,
% 3.51/3.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.51/3.71         (~ (v1_xboole_0 @ X22)
% 3.51/3.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 3.51/3.71          | (v1_xboole_0 @ X23))),
% 3.51/3.71      inference('cnf', [status(esa)], [cc3_relset_1])).
% 3.51/3.71  thf('4', plain,
% 3.51/3.71      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.71      inference('sup-', [status(thm)], ['2', '3'])).
% 3.51/3.71  thf(d3_tarski, axiom,
% 3.51/3.71    (![A:$i,B:$i]:
% 3.51/3.71     ( ( r1_tarski @ A @ B ) <=>
% 3.51/3.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.51/3.71  thf('5', plain,
% 3.51/3.71      (![X1 : $i, X3 : $i]:
% 3.51/3.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.51/3.71      inference('cnf', [status(esa)], [d3_tarski])).
% 3.51/3.71  thf(dt_k2_subset_1, axiom,
% 3.51/3.71    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 3.51/3.71  thf('6', plain,
% 3.51/3.71      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 3.51/3.71      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 3.51/3.71  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 3.51/3.71  thf('7', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 3.51/3.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 3.51/3.71  thf('8', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 3.51/3.71      inference('demod', [status(thm)], ['6', '7'])).
% 3.51/3.71  thf(t5_subset, axiom,
% 3.51/3.71    (![A:$i,B:$i,C:$i]:
% 3.51/3.71     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.51/3.71          ( v1_xboole_0 @ C ) ) ))).
% 3.51/3.71  thf('9', plain,
% 3.51/3.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.51/3.71         (~ (r2_hidden @ X9 @ X10)
% 3.51/3.71          | ~ (v1_xboole_0 @ X11)
% 3.51/3.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 3.51/3.71      inference('cnf', [status(esa)], [t5_subset])).
% 3.51/3.71  thf('10', plain,
% 3.51/3.71      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 3.51/3.71      inference('sup-', [status(thm)], ['8', '9'])).
% 3.51/3.71  thf('11', plain,
% 3.51/3.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.71      inference('sup-', [status(thm)], ['5', '10'])).
% 3.51/3.71  thf('12', plain,
% 3.51/3.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.71      inference('sup-', [status(thm)], ['5', '10'])).
% 3.51/3.71  thf(d10_xboole_0, axiom,
% 3.51/3.71    (![A:$i,B:$i]:
% 3.51/3.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.51/3.71  thf('13', plain,
% 3.51/3.71      (![X4 : $i, X6 : $i]:
% 3.51/3.71         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.51/3.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.51/3.71  thf('14', plain,
% 3.51/3.71      (![X0 : $i, X1 : $i]:
% 3.51/3.71         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.51/3.71      inference('sup-', [status(thm)], ['12', '13'])).
% 3.51/3.71  thf('15', plain,
% 3.51/3.71      (![X0 : $i, X1 : $i]:
% 3.51/3.71         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.71      inference('sup-', [status(thm)], ['11', '14'])).
% 3.51/3.71  thf('16', plain,
% 3.51/3.71      (![X0 : $i, X1 : $i]:
% 3.51/3.71         (~ (v1_xboole_0 @ X0)
% 3.51/3.71          | ((X1) = (k6_partfun1 @ X0))
% 3.51/3.71          | ~ (v1_xboole_0 @ X1))),
% 3.51/3.71      inference('sup-', [status(thm)], ['4', '15'])).
% 3.51/3.71  thf(fc4_funct_1, axiom,
% 3.51/3.71    (![A:$i]:
% 3.51/3.71     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.51/3.71       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.51/3.71  thf('17', plain, (![X15 : $i]: (v2_funct_1 @ (k6_relat_1 @ X15))),
% 3.51/3.71      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.51/3.71  thf('18', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 3.51/3.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.51/3.71  thf('19', plain, (![X15 : $i]: (v2_funct_1 @ (k6_partfun1 @ X15))),
% 3.51/3.71      inference('demod', [status(thm)], ['17', '18'])).
% 3.51/3.71  thf('20', plain,
% 3.51/3.71      (![X0 : $i, X1 : $i]:
% 3.51/3.71         ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.51/3.71      inference('sup+', [status(thm)], ['16', '19'])).
% 3.51/3.71  thf('21', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.71      inference('condensation', [status(thm)], ['20'])).
% 3.51/3.71  thf(t29_funct_2, conjecture,
% 3.51/3.71    (![A:$i,B:$i,C:$i]:
% 3.51/3.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.51/3.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.51/3.71       ( ![D:$i]:
% 3.51/3.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.51/3.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.51/3.71           ( ( r2_relset_1 @
% 3.51/3.71               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.51/3.71               ( k6_partfun1 @ A ) ) =>
% 3.51/3.71             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.51/3.71  thf(zf_stmt_0, negated_conjecture,
% 3.51/3.71    (~( ![A:$i,B:$i,C:$i]:
% 3.51/3.71        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.51/3.71            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.51/3.71          ( ![D:$i]:
% 3.51/3.71            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.51/3.71                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.51/3.71              ( ( r2_relset_1 @
% 3.51/3.71                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.51/3.71                  ( k6_partfun1 @ A ) ) =>
% 3.51/3.71                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.51/3.71    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.51/3.71  thf('22', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('23', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.51/3.71      inference('split', [status(esa)], ['22'])).
% 3.51/3.71  thf('24', plain,
% 3.51/3.71      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.51/3.71        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.51/3.71        (k6_partfun1 @ sk_A))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('25', plain,
% 3.51/3.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf(t24_funct_2, axiom,
% 3.51/3.71    (![A:$i,B:$i,C:$i]:
% 3.51/3.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.51/3.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.51/3.71       ( ![D:$i]:
% 3.51/3.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.51/3.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.51/3.71           ( ( r2_relset_1 @
% 3.51/3.71               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.51/3.71               ( k6_partfun1 @ B ) ) =>
% 3.51/3.71             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.51/3.71  thf('26', plain,
% 3.51/3.71      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 3.51/3.71         (~ (v1_funct_1 @ X45)
% 3.51/3.71          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 3.51/3.71          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 3.51/3.71          | ~ (r2_relset_1 @ X46 @ X46 @ 
% 3.51/3.71               (k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48) @ 
% 3.51/3.71               (k6_partfun1 @ X46))
% 3.51/3.71          | ((k2_relset_1 @ X47 @ X46 @ X48) = (X46))
% 3.51/3.71          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 3.51/3.71          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 3.51/3.71          | ~ (v1_funct_1 @ X48))),
% 3.51/3.71      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.51/3.71  thf('27', plain,
% 3.51/3.71      (![X0 : $i]:
% 3.51/3.71         (~ (v1_funct_1 @ X0)
% 3.51/3.71          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.51/3.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.51/3.71          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.51/3.71          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.51/3.71               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 3.51/3.71               (k6_partfun1 @ sk_A))
% 3.51/3.71          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 3.51/3.71          | ~ (v1_funct_1 @ sk_C_1))),
% 3.51/3.71      inference('sup-', [status(thm)], ['25', '26'])).
% 3.51/3.71  thf('28', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('29', plain, ((v1_funct_1 @ sk_C_1)),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('30', plain,
% 3.51/3.71      (![X0 : $i]:
% 3.51/3.71         (~ (v1_funct_1 @ X0)
% 3.51/3.71          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.51/3.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.51/3.71          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.51/3.71          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.51/3.71               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 3.51/3.71               (k6_partfun1 @ sk_A)))),
% 3.51/3.71      inference('demod', [status(thm)], ['27', '28', '29'])).
% 3.51/3.71  thf('31', plain,
% 3.51/3.71      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.51/3.71        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.51/3.71        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.51/3.71        | ~ (v1_funct_1 @ sk_D))),
% 3.51/3.71      inference('sup-', [status(thm)], ['24', '30'])).
% 3.51/3.71  thf('32', plain,
% 3.51/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf(redefinition_k2_relset_1, axiom,
% 3.51/3.71    (![A:$i,B:$i,C:$i]:
% 3.51/3.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.51/3.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.51/3.71  thf('33', plain,
% 3.51/3.71      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.51/3.71         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 3.51/3.71          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 3.51/3.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.51/3.71  thf('34', plain,
% 3.51/3.71      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.51/3.71      inference('sup-', [status(thm)], ['32', '33'])).
% 3.51/3.71  thf('35', plain,
% 3.51/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('36', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('38', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.51/3.71      inference('demod', [status(thm)], ['31', '34', '35', '36', '37'])).
% 3.51/3.71  thf('39', plain,
% 3.51/3.71      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 3.51/3.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.51/3.71  thf('40', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 3.51/3.71      inference('simplify', [status(thm)], ['39'])).
% 3.51/3.71  thf(d19_relat_1, axiom,
% 3.51/3.71    (![A:$i,B:$i]:
% 3.51/3.71     ( ( v1_relat_1 @ B ) =>
% 3.51/3.71       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.51/3.71  thf('41', plain,
% 3.51/3.71      (![X12 : $i, X13 : $i]:
% 3.51/3.71         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 3.51/3.71          | (v5_relat_1 @ X12 @ X13)
% 3.51/3.71          | ~ (v1_relat_1 @ X12))),
% 3.51/3.71      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.51/3.71  thf('42', plain,
% 3.51/3.71      (![X0 : $i]:
% 3.51/3.71         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.51/3.71      inference('sup-', [status(thm)], ['40', '41'])).
% 3.51/3.71  thf(d3_funct_2, axiom,
% 3.51/3.71    (![A:$i,B:$i]:
% 3.51/3.71     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.51/3.71       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.51/3.71  thf('43', plain,
% 3.51/3.71      (![X36 : $i, X37 : $i]:
% 3.51/3.71         (((k2_relat_1 @ X37) != (X36))
% 3.51/3.71          | (v2_funct_2 @ X37 @ X36)
% 3.51/3.71          | ~ (v5_relat_1 @ X37 @ X36)
% 3.51/3.71          | ~ (v1_relat_1 @ X37))),
% 3.51/3.71      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.51/3.71  thf('44', plain,
% 3.51/3.71      (![X37 : $i]:
% 3.51/3.71         (~ (v1_relat_1 @ X37)
% 3.51/3.71          | ~ (v5_relat_1 @ X37 @ (k2_relat_1 @ X37))
% 3.51/3.71          | (v2_funct_2 @ X37 @ (k2_relat_1 @ X37)))),
% 3.51/3.71      inference('simplify', [status(thm)], ['43'])).
% 3.51/3.71  thf('45', plain,
% 3.51/3.71      (![X0 : $i]:
% 3.51/3.71         (~ (v1_relat_1 @ X0)
% 3.51/3.71          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 3.51/3.71          | ~ (v1_relat_1 @ X0))),
% 3.51/3.71      inference('sup-', [status(thm)], ['42', '44'])).
% 3.51/3.71  thf('46', plain,
% 3.51/3.71      (![X0 : $i]:
% 3.51/3.71         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.51/3.71      inference('simplify', [status(thm)], ['45'])).
% 3.51/3.71  thf('47', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 3.51/3.71      inference('sup+', [status(thm)], ['38', '46'])).
% 3.51/3.71  thf('48', plain,
% 3.51/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf(cc1_relset_1, axiom,
% 3.51/3.71    (![A:$i,B:$i,C:$i]:
% 3.51/3.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.51/3.71       ( v1_relat_1 @ C ) ))).
% 3.51/3.71  thf('49', plain,
% 3.51/3.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.51/3.71         ((v1_relat_1 @ X16)
% 3.51/3.71          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.51/3.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.51/3.71  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 3.51/3.71      inference('sup-', [status(thm)], ['48', '49'])).
% 3.51/3.71  thf('51', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.51/3.71      inference('demod', [status(thm)], ['47', '50'])).
% 3.51/3.71  thf('52', plain,
% 3.51/3.71      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.51/3.71      inference('split', [status(esa)], ['22'])).
% 3.51/3.71  thf('53', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.51/3.71      inference('sup-', [status(thm)], ['51', '52'])).
% 3.51/3.71  thf('54', plain,
% 3.51/3.71      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.51/3.71      inference('split', [status(esa)], ['22'])).
% 3.51/3.71  thf('55', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 3.51/3.71      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 3.51/3.71  thf('56', plain, (~ (v2_funct_1 @ sk_C_1)),
% 3.51/3.71      inference('simpl_trail', [status(thm)], ['23', '55'])).
% 3.51/3.71  thf('57', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 3.51/3.71      inference('sup-', [status(thm)], ['21', '56'])).
% 3.51/3.71  thf('58', plain,
% 3.51/3.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('59', plain,
% 3.51/3.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.51/3.71         (~ (v1_xboole_0 @ X22)
% 3.51/3.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 3.51/3.71          | (v1_xboole_0 @ X23))),
% 3.51/3.71      inference('cnf', [status(esa)], [cc3_relset_1])).
% 3.51/3.71  thf('60', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_A))),
% 3.51/3.71      inference('sup-', [status(thm)], ['58', '59'])).
% 3.51/3.71  thf('61', plain,
% 3.51/3.71      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.51/3.71        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.51/3.71        (k6_partfun1 @ sk_A))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('62', plain,
% 3.51/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('63', plain,
% 3.51/3.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf(dt_k1_partfun1, axiom,
% 3.51/3.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.51/3.71     ( ( ( v1_funct_1 @ E ) & 
% 3.51/3.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.51/3.71         ( v1_funct_1 @ F ) & 
% 3.51/3.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.51/3.71       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.51/3.71         ( m1_subset_1 @
% 3.51/3.71           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.51/3.71           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.51/3.71  thf('64', plain,
% 3.51/3.71      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 3.51/3.71         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 3.51/3.71          | ~ (v1_funct_1 @ X38)
% 3.51/3.71          | ~ (v1_funct_1 @ X41)
% 3.51/3.71          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 3.51/3.71          | (m1_subset_1 @ (k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41) @ 
% 3.51/3.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X43))))),
% 3.51/3.71      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.51/3.71  thf('65', plain,
% 3.51/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.51/3.71         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 3.51/3.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.51/3.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.51/3.71          | ~ (v1_funct_1 @ X1)
% 3.51/3.71          | ~ (v1_funct_1 @ sk_C_1))),
% 3.51/3.71      inference('sup-', [status(thm)], ['63', '64'])).
% 3.51/3.71  thf('66', plain, ((v1_funct_1 @ sk_C_1)),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('67', plain,
% 3.51/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.51/3.71         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 3.51/3.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.51/3.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.51/3.71          | ~ (v1_funct_1 @ X1))),
% 3.51/3.71      inference('demod', [status(thm)], ['65', '66'])).
% 3.51/3.71  thf('68', plain,
% 3.51/3.71      ((~ (v1_funct_1 @ sk_D)
% 3.51/3.71        | (m1_subset_1 @ 
% 3.51/3.71           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.51/3.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.51/3.71      inference('sup-', [status(thm)], ['62', '67'])).
% 3.51/3.71  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('70', plain,
% 3.51/3.71      ((m1_subset_1 @ 
% 3.51/3.71        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.51/3.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.51/3.71      inference('demod', [status(thm)], ['68', '69'])).
% 3.51/3.71  thf(redefinition_r2_relset_1, axiom,
% 3.51/3.71    (![A:$i,B:$i,C:$i,D:$i]:
% 3.51/3.71     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.51/3.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.51/3.71       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.51/3.71  thf('71', plain,
% 3.51/3.71      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.51/3.71         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.51/3.71          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.51/3.71          | ((X31) = (X34))
% 3.51/3.71          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 3.51/3.71      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.51/3.71  thf('72', plain,
% 3.51/3.71      (![X0 : $i]:
% 3.51/3.71         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.51/3.71             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 3.51/3.71          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) = (X0))
% 3.51/3.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.51/3.71      inference('sup-', [status(thm)], ['70', '71'])).
% 3.51/3.71  thf('73', plain,
% 3.51/3.71      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.51/3.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.51/3.71        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 3.51/3.71            = (k6_partfun1 @ sk_A)))),
% 3.51/3.71      inference('sup-', [status(thm)], ['61', '72'])).
% 3.51/3.71  thf('74', plain,
% 3.51/3.71      (![X35 : $i]:
% 3.51/3.71         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 3.51/3.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 3.51/3.71      inference('demod', [status(thm)], ['0', '1'])).
% 3.51/3.71  thf('75', plain,
% 3.51/3.71      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 3.51/3.71         = (k6_partfun1 @ sk_A))),
% 3.51/3.71      inference('demod', [status(thm)], ['73', '74'])).
% 3.51/3.71  thf('76', plain,
% 3.51/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf(t26_funct_2, axiom,
% 3.51/3.71    (![A:$i,B:$i,C:$i,D:$i]:
% 3.51/3.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.51/3.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.51/3.71       ( ![E:$i]:
% 3.51/3.71         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.51/3.71             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.51/3.71           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.51/3.71             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.51/3.71               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.51/3.71  thf('77', plain,
% 3.51/3.71      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 3.51/3.71         (~ (v1_funct_1 @ X49)
% 3.51/3.71          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 3.51/3.71          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 3.51/3.71          | ~ (v2_funct_1 @ (k1_partfun1 @ X52 @ X50 @ X50 @ X51 @ X53 @ X49))
% 3.51/3.71          | (v2_funct_1 @ X53)
% 3.51/3.71          | ((X51) = (k1_xboole_0))
% 3.51/3.71          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 3.51/3.71          | ~ (v1_funct_2 @ X53 @ X52 @ X50)
% 3.51/3.71          | ~ (v1_funct_1 @ X53))),
% 3.51/3.71      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.51/3.71  thf('78', plain,
% 3.51/3.71      (![X0 : $i, X1 : $i]:
% 3.51/3.71         (~ (v1_funct_1 @ X0)
% 3.51/3.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.51/3.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.51/3.71          | ((sk_A) = (k1_xboole_0))
% 3.51/3.71          | (v2_funct_1 @ X0)
% 3.51/3.71          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.51/3.71          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.51/3.71          | ~ (v1_funct_1 @ sk_D))),
% 3.51/3.71      inference('sup-', [status(thm)], ['76', '77'])).
% 3.51/3.71  thf('79', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('81', plain,
% 3.51/3.71      (![X0 : $i, X1 : $i]:
% 3.51/3.71         (~ (v1_funct_1 @ X0)
% 3.51/3.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.51/3.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.51/3.71          | ((sk_A) = (k1_xboole_0))
% 3.51/3.71          | (v2_funct_1 @ X0)
% 3.51/3.71          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.51/3.71      inference('demod', [status(thm)], ['78', '79', '80'])).
% 3.51/3.71  thf('82', plain,
% 3.51/3.71      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.51/3.71        | (v2_funct_1 @ sk_C_1)
% 3.51/3.71        | ((sk_A) = (k1_xboole_0))
% 3.51/3.71        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.51/3.71        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 3.51/3.71        | ~ (v1_funct_1 @ sk_C_1))),
% 3.51/3.71      inference('sup-', [status(thm)], ['75', '81'])).
% 3.51/3.71  thf('83', plain, (![X15 : $i]: (v2_funct_1 @ (k6_partfun1 @ X15))),
% 3.51/3.71      inference('demod', [status(thm)], ['17', '18'])).
% 3.51/3.71  thf('84', plain,
% 3.51/3.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('85', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('86', plain, ((v1_funct_1 @ sk_C_1)),
% 3.51/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.71  thf('87', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 3.51/3.71      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 3.51/3.71  thf('88', plain, (~ (v2_funct_1 @ sk_C_1)),
% 3.51/3.71      inference('simpl_trail', [status(thm)], ['23', '55'])).
% 3.51/3.71  thf('89', plain, (((sk_A) = (k1_xboole_0))),
% 3.51/3.71      inference('clc', [status(thm)], ['87', '88'])).
% 3.51/3.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.51/3.71  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.71  thf('91', plain, ((v1_xboole_0 @ sk_C_1)),
% 3.51/3.71      inference('demod', [status(thm)], ['60', '89', '90'])).
% 3.51/3.71  thf('92', plain, ($false), inference('demod', [status(thm)], ['57', '91'])).
% 3.51/3.71  
% 3.51/3.71  % SZS output end Refutation
% 3.51/3.71  
% 3.51/3.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
