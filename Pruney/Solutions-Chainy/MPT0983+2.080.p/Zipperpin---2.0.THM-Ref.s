%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SavPyrmv9y

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:13 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 344 expanded)
%              Number of leaves         :   43 ( 119 expanded)
%              Depth                    :   15
%              Number of atoms          : 1177 (6698 expanded)
%              Number of equality atoms :   33 (  82 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('2',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['15'])).

thf('17',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_partfun1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('22',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_relat_1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['28','31','32','33','34'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ X27 )
       != X26 )
      | ( v2_funct_2 @ X27 @ X26 )
      | ~ ( v5_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('37',plain,(
    ! [X27: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v5_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
      | ( v2_funct_2 @ X27 @ ( k2_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['28','31','32','33','34'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['38','41','42','45'])).

thf('47',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('48',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('50',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['16','50'])).

thf('52',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('68',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('72',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
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

thf('74',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X44 @ X42 @ X42 @ X43 @ X45 @ X41 ) )
      | ( v2_funct_1 @ X45 )
      | ( X43 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X42 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('86',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('87',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['84','87'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','88','89'])).

thf('91',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['52','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['51','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SavPyrmv9y
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.42/2.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.42/2.62  % Solved by: fo/fo7.sh
% 2.42/2.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.42/2.62  % done 2755 iterations in 2.174s
% 2.42/2.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.42/2.62  % SZS output start Refutation
% 2.42/2.62  thf(sk_D_type, type, sk_D: $i).
% 2.42/2.62  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.42/2.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.42/2.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.42/2.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.42/2.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.42/2.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.42/2.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.42/2.62  thf(sk_B_type, type, sk_B: $i > $i).
% 2.42/2.62  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.42/2.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.42/2.62  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.42/2.62  thf(sk_C_type, type, sk_C: $i).
% 2.42/2.62  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.42/2.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.42/2.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.42/2.62  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.42/2.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.42/2.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.42/2.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.42/2.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.42/2.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.42/2.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.42/2.62  thf(sk_A_type, type, sk_A: $i).
% 2.42/2.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.42/2.62  thf(d1_xboole_0, axiom,
% 2.42/2.62    (![A:$i]:
% 2.42/2.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.42/2.62  thf('0', plain,
% 2.42/2.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.42/2.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.42/2.62  thf(fc3_zfmisc_1, axiom,
% 2.42/2.62    (![A:$i,B:$i]:
% 2.42/2.62     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.42/2.62  thf('1', plain,
% 2.42/2.62      (![X5 : $i, X6 : $i]:
% 2.42/2.62         ((v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)) | ~ (v1_xboole_0 @ X6))),
% 2.42/2.62      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 2.42/2.62  thf(dt_k6_partfun1, axiom,
% 2.42/2.62    (![A:$i]:
% 2.42/2.62     ( ( m1_subset_1 @
% 2.42/2.62         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.42/2.62       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.42/2.62  thf('2', plain,
% 2.42/2.62      (![X35 : $i]:
% 2.42/2.62         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 2.42/2.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 2.42/2.62      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.42/2.62  thf(redefinition_k6_partfun1, axiom,
% 2.42/2.62    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.42/2.62  thf('3', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 2.42/2.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.42/2.62  thf('4', plain,
% 2.42/2.62      (![X35 : $i]:
% 2.42/2.62         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 2.42/2.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 2.42/2.62      inference('demod', [status(thm)], ['2', '3'])).
% 2.42/2.62  thf(t5_subset, axiom,
% 2.42/2.62    (![A:$i,B:$i,C:$i]:
% 2.42/2.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.42/2.62          ( v1_xboole_0 @ C ) ) ))).
% 2.42/2.62  thf('5', plain,
% 2.42/2.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.42/2.62         (~ (r2_hidden @ X9 @ X10)
% 2.42/2.62          | ~ (v1_xboole_0 @ X11)
% 2.42/2.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.42/2.62      inference('cnf', [status(esa)], [t5_subset])).
% 2.42/2.62  thf('6', plain,
% 2.42/2.62      (![X0 : $i, X1 : $i]:
% 2.42/2.62         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 2.42/2.62          | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 2.42/2.62      inference('sup-', [status(thm)], ['4', '5'])).
% 2.42/2.62  thf('7', plain,
% 2.42/2.62      (![X0 : $i, X1 : $i]:
% 2.42/2.62         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 2.42/2.62      inference('sup-', [status(thm)], ['1', '6'])).
% 2.42/2.62  thf('8', plain,
% 2.42/2.62      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.42/2.62      inference('sup-', [status(thm)], ['0', '7'])).
% 2.42/2.62  thf(t8_boole, axiom,
% 2.42/2.62    (![A:$i,B:$i]:
% 2.42/2.62     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.42/2.62  thf('9', plain,
% 2.42/2.62      (![X3 : $i, X4 : $i]:
% 2.42/2.62         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 2.42/2.62      inference('cnf', [status(esa)], [t8_boole])).
% 2.42/2.62  thf('10', plain,
% 2.42/2.62      (![X0 : $i, X1 : $i]:
% 2.42/2.62         (~ (v1_xboole_0 @ X0)
% 2.42/2.62          | ((k6_relat_1 @ X0) = (X1))
% 2.42/2.62          | ~ (v1_xboole_0 @ X1))),
% 2.42/2.62      inference('sup-', [status(thm)], ['8', '9'])).
% 2.42/2.62  thf(t29_funct_2, conjecture,
% 2.42/2.62    (![A:$i,B:$i,C:$i]:
% 2.42/2.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.42/2.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.42/2.62       ( ![D:$i]:
% 2.42/2.62         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.42/2.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.42/2.62           ( ( r2_relset_1 @
% 2.42/2.62               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.42/2.62               ( k6_partfun1 @ A ) ) =>
% 2.42/2.62             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.42/2.62  thf(zf_stmt_0, negated_conjecture,
% 2.42/2.62    (~( ![A:$i,B:$i,C:$i]:
% 2.42/2.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.42/2.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.42/2.62          ( ![D:$i]:
% 2.42/2.62            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.42/2.62                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.42/2.62              ( ( r2_relset_1 @
% 2.42/2.62                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.42/2.62                  ( k6_partfun1 @ A ) ) =>
% 2.42/2.62                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.42/2.62    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.42/2.62  thf('11', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('12', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.42/2.62      inference('split', [status(esa)], ['11'])).
% 2.42/2.62  thf('13', plain,
% 2.42/2.62      ((![X0 : $i]:
% 2.42/2.62          (~ (v2_funct_1 @ (k6_relat_1 @ X0))
% 2.42/2.62           | ~ (v1_xboole_0 @ sk_C)
% 2.42/2.62           | ~ (v1_xboole_0 @ X0)))
% 2.42/2.62         <= (~ ((v2_funct_1 @ sk_C)))),
% 2.42/2.62      inference('sup-', [status(thm)], ['10', '12'])).
% 2.42/2.62  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.42/2.62  thf('14', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 2.42/2.62      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.42/2.62  thf('15', plain,
% 2.42/2.62      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 2.42/2.62         <= (~ ((v2_funct_1 @ sk_C)))),
% 2.42/2.62      inference('demod', [status(thm)], ['13', '14'])).
% 2.42/2.62  thf('16', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.42/2.62      inference('condensation', [status(thm)], ['15'])).
% 2.42/2.62  thf('17', plain,
% 2.42/2.62      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.42/2.62        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.42/2.62        (k6_partfun1 @ sk_A))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('18', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 2.42/2.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.42/2.62  thf('19', plain,
% 2.42/2.62      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.42/2.62        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.42/2.62        (k6_relat_1 @ sk_A))),
% 2.42/2.62      inference('demod', [status(thm)], ['17', '18'])).
% 2.42/2.62  thf('20', plain,
% 2.42/2.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf(t24_funct_2, axiom,
% 2.42/2.62    (![A:$i,B:$i,C:$i]:
% 2.42/2.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.42/2.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.42/2.62       ( ![D:$i]:
% 2.42/2.62         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.42/2.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.42/2.62           ( ( r2_relset_1 @
% 2.42/2.62               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.42/2.62               ( k6_partfun1 @ B ) ) =>
% 2.42/2.62             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.42/2.62  thf('21', plain,
% 2.42/2.62      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.42/2.62         (~ (v1_funct_1 @ X37)
% 2.42/2.62          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 2.42/2.62          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.42/2.62          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 2.42/2.62               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 2.42/2.62               (k6_partfun1 @ X38))
% 2.42/2.62          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 2.42/2.62          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 2.42/2.62          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 2.42/2.62          | ~ (v1_funct_1 @ X40))),
% 2.42/2.62      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.42/2.62  thf('22', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 2.42/2.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.42/2.62  thf('23', plain,
% 2.42/2.62      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.42/2.62         (~ (v1_funct_1 @ X37)
% 2.42/2.62          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 2.42/2.62          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.42/2.62          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 2.42/2.62               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 2.42/2.62               (k6_relat_1 @ X38))
% 2.42/2.62          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 2.42/2.62          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 2.42/2.62          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 2.42/2.62          | ~ (v1_funct_1 @ X40))),
% 2.42/2.62      inference('demod', [status(thm)], ['21', '22'])).
% 2.42/2.62  thf('24', plain,
% 2.42/2.62      (![X0 : $i]:
% 2.42/2.62         (~ (v1_funct_1 @ X0)
% 2.42/2.62          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 2.42/2.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 2.42/2.62          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 2.42/2.62          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.42/2.62               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 2.42/2.62               (k6_relat_1 @ sk_A))
% 2.42/2.62          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 2.42/2.62          | ~ (v1_funct_1 @ sk_C))),
% 2.42/2.62      inference('sup-', [status(thm)], ['20', '23'])).
% 2.42/2.62  thf('25', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('27', plain,
% 2.42/2.62      (![X0 : $i]:
% 2.42/2.62         (~ (v1_funct_1 @ X0)
% 2.42/2.62          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 2.42/2.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 2.42/2.62          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 2.42/2.62          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.42/2.62               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 2.42/2.62               (k6_relat_1 @ sk_A)))),
% 2.42/2.62      inference('demod', [status(thm)], ['24', '25', '26'])).
% 2.42/2.62  thf('28', plain,
% 2.42/2.62      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 2.42/2.62        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 2.42/2.62        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 2.42/2.62        | ~ (v1_funct_1 @ sk_D))),
% 2.42/2.62      inference('sup-', [status(thm)], ['19', '27'])).
% 2.42/2.62  thf('29', plain,
% 2.42/2.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf(redefinition_k2_relset_1, axiom,
% 2.42/2.62    (![A:$i,B:$i,C:$i]:
% 2.42/2.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.42/2.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.42/2.62  thf('30', plain,
% 2.42/2.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.42/2.62         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 2.42/2.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.42/2.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.42/2.62  thf('31', plain,
% 2.42/2.62      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.42/2.62      inference('sup-', [status(thm)], ['29', '30'])).
% 2.42/2.62  thf('32', plain,
% 2.42/2.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('33', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('35', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.42/2.62      inference('demod', [status(thm)], ['28', '31', '32', '33', '34'])).
% 2.42/2.62  thf(d3_funct_2, axiom,
% 2.42/2.62    (![A:$i,B:$i]:
% 2.42/2.62     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.42/2.62       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.42/2.62  thf('36', plain,
% 2.42/2.62      (![X26 : $i, X27 : $i]:
% 2.42/2.62         (((k2_relat_1 @ X27) != (X26))
% 2.42/2.62          | (v2_funct_2 @ X27 @ X26)
% 2.42/2.62          | ~ (v5_relat_1 @ X27 @ X26)
% 2.42/2.62          | ~ (v1_relat_1 @ X27))),
% 2.42/2.62      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.42/2.62  thf('37', plain,
% 2.42/2.62      (![X27 : $i]:
% 2.42/2.62         (~ (v1_relat_1 @ X27)
% 2.42/2.62          | ~ (v5_relat_1 @ X27 @ (k2_relat_1 @ X27))
% 2.42/2.62          | (v2_funct_2 @ X27 @ (k2_relat_1 @ X27)))),
% 2.42/2.62      inference('simplify', [status(thm)], ['36'])).
% 2.42/2.62  thf('38', plain,
% 2.42/2.62      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.42/2.62        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.42/2.62        | ~ (v1_relat_1 @ sk_D))),
% 2.42/2.62      inference('sup-', [status(thm)], ['35', '37'])).
% 2.42/2.62  thf('39', plain,
% 2.42/2.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf(cc2_relset_1, axiom,
% 2.42/2.62    (![A:$i,B:$i,C:$i]:
% 2.42/2.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.42/2.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.42/2.62  thf('40', plain,
% 2.42/2.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.42/2.62         ((v5_relat_1 @ X16 @ X18)
% 2.42/2.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.42/2.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.42/2.62  thf('41', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.42/2.62      inference('sup-', [status(thm)], ['39', '40'])).
% 2.42/2.62  thf('42', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.42/2.62      inference('demod', [status(thm)], ['28', '31', '32', '33', '34'])).
% 2.42/2.62  thf('43', plain,
% 2.42/2.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf(cc1_relset_1, axiom,
% 2.42/2.62    (![A:$i,B:$i,C:$i]:
% 2.42/2.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.42/2.62       ( v1_relat_1 @ C ) ))).
% 2.42/2.62  thf('44', plain,
% 2.42/2.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.42/2.62         ((v1_relat_1 @ X13)
% 2.42/2.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.42/2.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.42/2.62  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 2.42/2.62      inference('sup-', [status(thm)], ['43', '44'])).
% 2.42/2.62  thf('46', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.42/2.62      inference('demod', [status(thm)], ['38', '41', '42', '45'])).
% 2.42/2.62  thf('47', plain,
% 2.42/2.62      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.42/2.62      inference('split', [status(esa)], ['11'])).
% 2.42/2.62  thf('48', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.42/2.62      inference('sup-', [status(thm)], ['46', '47'])).
% 2.42/2.62  thf('49', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.42/2.62      inference('split', [status(esa)], ['11'])).
% 2.42/2.62  thf('50', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.42/2.62      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 2.42/2.62  thf('51', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.42/2.62      inference('simpl_trail', [status(thm)], ['16', '50'])).
% 2.42/2.62  thf('52', plain,
% 2.42/2.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.42/2.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.42/2.62  thf(fc4_zfmisc_1, axiom,
% 2.42/2.62    (![A:$i,B:$i]:
% 2.42/2.62     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.42/2.62  thf('53', plain,
% 2.42/2.62      (![X7 : $i, X8 : $i]:
% 2.42/2.62         (~ (v1_xboole_0 @ X7) | (v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 2.42/2.62      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.42/2.62  thf('54', plain,
% 2.42/2.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('55', plain,
% 2.42/2.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.42/2.62         (~ (r2_hidden @ X9 @ X10)
% 2.42/2.62          | ~ (v1_xboole_0 @ X11)
% 2.42/2.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.42/2.62      inference('cnf', [status(esa)], [t5_subset])).
% 2.42/2.62  thf('56', plain,
% 2.42/2.62      (![X0 : $i]:
% 2.42/2.62         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.42/2.62          | ~ (r2_hidden @ X0 @ sk_C))),
% 2.42/2.62      inference('sup-', [status(thm)], ['54', '55'])).
% 2.42/2.62  thf('57', plain,
% 2.42/2.62      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C))),
% 2.42/2.62      inference('sup-', [status(thm)], ['53', '56'])).
% 2.42/2.62  thf('58', plain,
% 2.42/2.62      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.42/2.62        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.42/2.62        (k6_relat_1 @ sk_A))),
% 2.42/2.62      inference('demod', [status(thm)], ['17', '18'])).
% 2.42/2.62  thf('59', plain,
% 2.42/2.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('60', plain,
% 2.42/2.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf(dt_k1_partfun1, axiom,
% 2.42/2.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.42/2.62     ( ( ( v1_funct_1 @ E ) & 
% 2.42/2.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.42/2.62         ( v1_funct_1 @ F ) & 
% 2.42/2.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.42/2.62       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.42/2.62         ( m1_subset_1 @
% 2.42/2.62           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.42/2.62           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.42/2.62  thf('61', plain,
% 2.42/2.62      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.42/2.62         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.42/2.62          | ~ (v1_funct_1 @ X28)
% 2.42/2.62          | ~ (v1_funct_1 @ X31)
% 2.42/2.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.42/2.62          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 2.42/2.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 2.42/2.62      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.42/2.62  thf('62', plain,
% 2.42/2.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.62         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 2.42/2.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.42/2.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.42/2.62          | ~ (v1_funct_1 @ X1)
% 2.42/2.62          | ~ (v1_funct_1 @ sk_C))),
% 2.42/2.62      inference('sup-', [status(thm)], ['60', '61'])).
% 2.42/2.62  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('64', plain,
% 2.42/2.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.62         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 2.42/2.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.42/2.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.42/2.62          | ~ (v1_funct_1 @ X1))),
% 2.42/2.62      inference('demod', [status(thm)], ['62', '63'])).
% 2.42/2.62  thf('65', plain,
% 2.42/2.62      ((~ (v1_funct_1 @ sk_D)
% 2.42/2.62        | (m1_subset_1 @ 
% 2.42/2.62           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.42/2.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.42/2.62      inference('sup-', [status(thm)], ['59', '64'])).
% 2.42/2.62  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('67', plain,
% 2.42/2.62      ((m1_subset_1 @ 
% 2.42/2.62        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.42/2.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.42/2.62      inference('demod', [status(thm)], ['65', '66'])).
% 2.42/2.62  thf(redefinition_r2_relset_1, axiom,
% 2.42/2.62    (![A:$i,B:$i,C:$i,D:$i]:
% 2.42/2.62     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.42/2.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.42/2.62       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.42/2.62  thf('68', plain,
% 2.42/2.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.42/2.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.42/2.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.42/2.62          | ((X22) = (X25))
% 2.42/2.62          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 2.42/2.62      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.42/2.62  thf('69', plain,
% 2.42/2.62      (![X0 : $i]:
% 2.42/2.62         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.42/2.62             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 2.42/2.62          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 2.42/2.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.42/2.62      inference('sup-', [status(thm)], ['67', '68'])).
% 2.42/2.62  thf('70', plain,
% 2.42/2.62      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.42/2.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.42/2.62        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 2.42/2.62            = (k6_relat_1 @ sk_A)))),
% 2.42/2.62      inference('sup-', [status(thm)], ['58', '69'])).
% 2.42/2.62  thf('71', plain,
% 2.42/2.62      (![X35 : $i]:
% 2.42/2.62         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 2.42/2.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 2.42/2.62      inference('demod', [status(thm)], ['2', '3'])).
% 2.42/2.62  thf('72', plain,
% 2.42/2.62      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 2.42/2.62         = (k6_relat_1 @ sk_A))),
% 2.42/2.62      inference('demod', [status(thm)], ['70', '71'])).
% 2.42/2.62  thf('73', plain,
% 2.42/2.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf(t26_funct_2, axiom,
% 2.42/2.62    (![A:$i,B:$i,C:$i,D:$i]:
% 2.42/2.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.42/2.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.42/2.62       ( ![E:$i]:
% 2.42/2.62         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.42/2.62             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.42/2.62           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.42/2.62             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.42/2.62               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.42/2.62  thf('74', plain,
% 2.42/2.62      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 2.42/2.62         (~ (v1_funct_1 @ X41)
% 2.42/2.62          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 2.42/2.62          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 2.42/2.62          | ~ (v2_funct_1 @ (k1_partfun1 @ X44 @ X42 @ X42 @ X43 @ X45 @ X41))
% 2.42/2.62          | (v2_funct_1 @ X45)
% 2.42/2.62          | ((X43) = (k1_xboole_0))
% 2.42/2.62          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 2.42/2.62          | ~ (v1_funct_2 @ X45 @ X44 @ X42)
% 2.42/2.62          | ~ (v1_funct_1 @ X45))),
% 2.42/2.62      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.42/2.62  thf('75', plain,
% 2.42/2.62      (![X0 : $i, X1 : $i]:
% 2.42/2.62         (~ (v1_funct_1 @ X0)
% 2.42/2.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 2.42/2.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 2.42/2.62          | ((sk_A) = (k1_xboole_0))
% 2.42/2.62          | (v2_funct_1 @ X0)
% 2.42/2.62          | ~ (v2_funct_1 @ 
% 2.42/2.62               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 2.42/2.62          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 2.42/2.62          | ~ (v1_funct_1 @ sk_D))),
% 2.42/2.62      inference('sup-', [status(thm)], ['73', '74'])).
% 2.42/2.62  thf('76', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('77', plain, ((v1_funct_1 @ sk_D)),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('78', plain,
% 2.42/2.62      (![X0 : $i, X1 : $i]:
% 2.42/2.62         (~ (v1_funct_1 @ X0)
% 2.42/2.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 2.42/2.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 2.42/2.62          | ((sk_A) = (k1_xboole_0))
% 2.42/2.62          | (v2_funct_1 @ X0)
% 2.42/2.62          | ~ (v2_funct_1 @ 
% 2.42/2.62               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 2.42/2.62      inference('demod', [status(thm)], ['75', '76', '77'])).
% 2.42/2.62  thf('79', plain,
% 2.42/2.62      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.42/2.62        | (v2_funct_1 @ sk_C)
% 2.42/2.62        | ((sk_A) = (k1_xboole_0))
% 2.42/2.62        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 2.42/2.62        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 2.42/2.62        | ~ (v1_funct_1 @ sk_C))),
% 2.42/2.62      inference('sup-', [status(thm)], ['72', '78'])).
% 2.42/2.62  thf('80', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 2.42/2.62      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.42/2.62  thf('81', plain,
% 2.42/2.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('82', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('84', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.42/2.62      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 2.42/2.62  thf('85', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.42/2.62      inference('split', [status(esa)], ['11'])).
% 2.42/2.62  thf('86', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.42/2.62      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 2.42/2.62  thf('87', plain, (~ (v2_funct_1 @ sk_C)),
% 2.42/2.62      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 2.42/2.62  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 2.42/2.62      inference('clc', [status(thm)], ['84', '87'])).
% 2.42/2.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.42/2.62  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.42/2.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.42/2.62  thf('90', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 2.42/2.62      inference('demod', [status(thm)], ['57', '88', '89'])).
% 2.42/2.62  thf('91', plain, ((v1_xboole_0 @ sk_C)),
% 2.42/2.62      inference('sup-', [status(thm)], ['52', '90'])).
% 2.42/2.62  thf('92', plain, ($false), inference('demod', [status(thm)], ['51', '91'])).
% 2.42/2.62  
% 2.42/2.62  % SZS output end Refutation
% 2.42/2.62  
% 2.42/2.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
