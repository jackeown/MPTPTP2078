%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jk3rHohNLQ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:20 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  231 (1832 expanded)
%              Number of leaves         :   44 ( 583 expanded)
%              Depth                    :   23
%              Number of atoms          : 2070 (40160 expanded)
%              Number of equality atoms :   74 ( 301 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t88_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
        & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
          & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_funct_2])).

thf('0',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k2_funct_2 @ X37 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X36 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) )
      | ~ ( v3_funct_2 @ X27 @ X26 @ X26 )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X26 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) )
      | ~ ( v3_funct_2 @ X27 @ X26 @ X26 )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X26 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('31',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X13 ) @ X13 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('38',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['38','39','40'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('42',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_2 @ X25 @ X24 )
      | ( ( k2_relat_1 @ X25 )
        = X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X13 ) @ X13 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('54',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('55',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('62',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('68',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','65','66','67'])).

thf('69',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('70',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('75',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('76',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('77',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('82',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','78','79','80','81'])).

thf('83',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','82'])).

thf('84',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('85',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('91',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('103',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('104',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('105',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('106',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['104','105'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('107',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_B )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('110',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('113',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['108','113'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('115',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('116',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('118',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('119',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X26 @ X27 ) @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) )
      | ~ ( v3_funct_2 @ X27 @ X26 @ X26 )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X26 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('127',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('129',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['119','127','128'])).

thf('130',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_2 @ X25 @ X24 )
      | ( ( k2_relat_1 @ X25 )
        = X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('131',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('133',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('134',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('135',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['131','132','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('138',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('139',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('141',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('144',plain,(
    v4_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('146',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_B
      = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('148',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('150',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('152',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('153',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('155',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['154'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('156',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X12 ) @ ( k9_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['153','157'])).

thf('159',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('160',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('162',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['158','159','160','161'])).

thf('163',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('164',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['116','136','162','163'])).

thf('165',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('166',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['164','167'])).

thf('169',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['116','136','162','163'])).

thf('170',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('171',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('173',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169','170','171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('175',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','175'])).

thf('177',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['116','136','162','163'])).

thf('178',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('179',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('180',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('182',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['176','177','178','179','180','181'])).

thf('183',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('185',plain,(
    $false ),
    inference(demod,[status(thm)],['94','183','184'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jk3rHohNLQ
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 970 iterations in 0.563s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.98  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.76/0.98  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.76/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.98  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.76/0.98  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.76/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.98  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.76/0.98  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.76/0.98  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.76/0.98  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.76/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.98  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.76/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.98  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.76/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.98  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.76/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.98  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.76/0.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.76/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.98  thf(t88_funct_2, conjecture,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.76/0.98         ( v3_funct_2 @ B @ A @ A ) & 
% 0.76/0.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.76/0.98       ( ( r2_relset_1 @
% 0.76/0.98           A @ A @ 
% 0.76/0.98           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.76/0.98           ( k6_partfun1 @ A ) ) & 
% 0.76/0.98         ( r2_relset_1 @
% 0.76/0.98           A @ A @ 
% 0.76/0.98           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.76/0.98           ( k6_partfun1 @ A ) ) ) ))).
% 0.76/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.98    (~( ![A:$i,B:$i]:
% 0.76/0.98        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.76/0.98            ( v3_funct_2 @ B @ A @ A ) & 
% 0.76/0.98            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.76/0.98          ( ( r2_relset_1 @
% 0.76/0.98              A @ A @ 
% 0.76/0.98              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.76/0.98              ( k6_partfun1 @ A ) ) & 
% 0.76/0.98            ( r2_relset_1 @
% 0.76/0.98              A @ A @ 
% 0.76/0.98              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.76/0.98              ( k6_partfun1 @ A ) ) ) ) )),
% 0.76/0.98    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.76/0.98  thf('0', plain,
% 0.76/0.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.76/0.98            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.76/0.98           (k6_partfun1 @ sk_A))
% 0.76/0.98        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.76/0.98              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.76/0.98             (k6_partfun1 @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('1', plain,
% 0.76/0.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.76/0.98            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.76/0.98           (k6_partfun1 @ sk_A)))
% 0.76/0.98         <= (~
% 0.76/0.98             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.76/0.98                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.76/0.98               (k6_partfun1 @ sk_A))))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf(redefinition_k6_partfun1, axiom,
% 0.76/0.98    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.76/0.98  thf('2', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.98  thf('3', plain,
% 0.76/0.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.76/0.98            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.76/0.98           (k6_relat_1 @ sk_A)))
% 0.76/0.98         <= (~
% 0.76/0.98             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.76/0.98                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.76/0.98               (k6_partfun1 @ sk_A))))),
% 0.76/0.98      inference('demod', [status(thm)], ['1', '2'])).
% 0.76/0.98  thf('4', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(redefinition_k2_funct_2, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.76/0.98         ( v3_funct_2 @ B @ A @ A ) & 
% 0.76/0.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.76/0.98       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.76/0.98  thf('5', plain,
% 0.76/0.98      (![X36 : $i, X37 : $i]:
% 0.76/0.98         (((k2_funct_2 @ X37 @ X36) = (k2_funct_1 @ X36))
% 0.76/0.98          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 0.76/0.98          | ~ (v3_funct_2 @ X36 @ X37 @ X37)
% 0.76/0.98          | ~ (v1_funct_2 @ X36 @ X37 @ X37)
% 0.76/0.98          | ~ (v1_funct_1 @ X36))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.76/0.98  thf('6', plain,
% 0.76/0.98      ((~ (v1_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.76/0.98        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.76/0.98        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.98  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.76/0.98  thf('11', plain,
% 0.76/0.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.76/0.98            (k2_funct_1 @ sk_B)) @ 
% 0.76/0.98           (k6_relat_1 @ sk_A)))
% 0.76/0.98         <= (~
% 0.76/0.98             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.76/0.98                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.76/0.98               (k6_partfun1 @ sk_A))))),
% 0.76/0.98      inference('demod', [status(thm)], ['3', '10'])).
% 0.76/0.98  thf('12', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('13', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(dt_k2_funct_2, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.76/0.98         ( v3_funct_2 @ B @ A @ A ) & 
% 0.76/0.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.76/0.98       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.76/0.98         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.76/0.98         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.76/0.98         ( m1_subset_1 @
% 0.76/0.98           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.76/0.98  thf('14', plain,
% 0.76/0.98      (![X26 : $i, X27 : $i]:
% 0.76/0.98         ((m1_subset_1 @ (k2_funct_2 @ X26 @ X27) @ 
% 0.76/0.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))
% 0.76/0.98          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))
% 0.76/0.98          | ~ (v3_funct_2 @ X27 @ X26 @ X26)
% 0.76/0.98          | ~ (v1_funct_2 @ X27 @ X26 @ X26)
% 0.76/0.98          | ~ (v1_funct_1 @ X27))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.76/0.98  thf('15', plain,
% 0.76/0.98      ((~ (v1_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.76/0.98        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.76/0.98        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.76/0.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.98  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('19', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.76/0.98  thf('20', plain,
% 0.76/0.98      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.76/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.76/0.98  thf(redefinition_k1_partfun1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.76/0.98     ( ( ( v1_funct_1 @ E ) & 
% 0.76/0.98         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.98         ( v1_funct_1 @ F ) & 
% 0.76/0.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.76/0.98       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.76/0.98  thf('21', plain,
% 0.76/0.98      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.76/0.98          | ~ (v1_funct_1 @ X30)
% 0.76/0.98          | ~ (v1_funct_1 @ X33)
% 0.76/0.98          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.76/0.98          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 0.76/0.98              = (k5_relat_1 @ X30 @ X33)))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.76/0.98  thf('22', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.76/0.98            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.76/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.76/0.98          | ~ (v1_funct_1 @ X0)
% 0.76/0.98          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['20', '21'])).
% 0.76/0.98  thf('23', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('24', plain,
% 0.76/0.98      (![X26 : $i, X27 : $i]:
% 0.76/0.98         ((v1_funct_1 @ (k2_funct_2 @ X26 @ X27))
% 0.76/0.98          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))
% 0.76/0.98          | ~ (v3_funct_2 @ X27 @ X26 @ X26)
% 0.76/0.98          | ~ (v1_funct_2 @ X27 @ X26 @ X26)
% 0.76/0.98          | ~ (v1_funct_1 @ X27))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.76/0.98  thf('25', plain,
% 0.76/0.98      ((~ (v1_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.76/0.98        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.76/0.98        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['23', '24'])).
% 0.76/0.98  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.76/0.98  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.76/0.98  thf('31', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['29', '30'])).
% 0.76/0.98  thf('32', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.76/0.98            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.76/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.76/0.98          | ~ (v1_funct_1 @ X0))),
% 0.76/0.98      inference('demod', [status(thm)], ['22', '31'])).
% 0.76/0.98  thf('33', plain,
% 0.76/0.98      ((~ (v1_funct_1 @ sk_B)
% 0.76/0.98        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.76/0.98            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['12', '32'])).
% 0.76/0.98  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(t61_funct_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.98       ( ( v2_funct_1 @ A ) =>
% 0.76/0.98         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.76/0.98             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.76/0.98           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.76/0.98             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.76/0.98  thf('35', plain,
% 0.76/0.98      (![X13 : $i]:
% 0.76/0.98         (~ (v2_funct_1 @ X13)
% 0.76/0.98          | ((k5_relat_1 @ (k2_funct_1 @ X13) @ X13)
% 0.76/0.98              = (k6_relat_1 @ (k2_relat_1 @ X13)))
% 0.76/0.98          | ~ (v1_funct_1 @ X13)
% 0.76/0.98          | ~ (v1_relat_1 @ X13))),
% 0.76/0.98      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.76/0.98  thf('36', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_funct_2, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.76/0.98         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.76/0.98  thf('37', plain,
% 0.76/0.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.76/0.98         (~ (v1_funct_1 @ X21)
% 0.76/0.98          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.76/0.98          | (v2_funct_2 @ X21 @ X23)
% 0.76/0.98          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.76/0.98  thf('38', plain,
% 0.76/0.98      (((v2_funct_2 @ sk_B @ sk_A)
% 0.76/0.98        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.76/0.98        | ~ (v1_funct_1 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/0.98  thf('39', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('41', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.76/0.98      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.76/0.98  thf(d3_funct_2, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.76/0.98       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.76/0.98  thf('42', plain,
% 0.76/0.98      (![X24 : $i, X25 : $i]:
% 0.76/0.98         (~ (v2_funct_2 @ X25 @ X24)
% 0.76/0.98          | ((k2_relat_1 @ X25) = (X24))
% 0.76/0.98          | ~ (v5_relat_1 @ X25 @ X24)
% 0.76/0.98          | ~ (v1_relat_1 @ X25))),
% 0.76/0.98      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.76/0.98  thf('43', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ sk_B)
% 0.76/0.98        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.76/0.98        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/0.98  thf('44', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/0.98  thf('45', plain,
% 0.76/0.98      (![X3 : $i, X4 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.76/0.98          | (v1_relat_1 @ X3)
% 0.76/0.98          | ~ (v1_relat_1 @ X4))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.98  thf('46', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['44', '45'])).
% 0.76/0.98  thf(fc6_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.98  thf('47', plain,
% 0.76/0.98      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.98  thf('49', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.98  thf('50', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.98         ((v5_relat_1 @ X14 @ X16)
% 0.76/0.98          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.98  thf('51', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.76/0.98      inference('sup-', [status(thm)], ['49', '50'])).
% 0.76/0.98  thf('52', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['43', '48', '51'])).
% 0.76/0.98  thf('53', plain,
% 0.76/0.98      (![X13 : $i]:
% 0.76/0.98         (~ (v2_funct_1 @ X13)
% 0.76/0.98          | ((k5_relat_1 @ (k2_funct_1 @ X13) @ X13)
% 0.76/0.98              = (k6_relat_1 @ (k2_relat_1 @ X13)))
% 0.76/0.98          | ~ (v1_funct_1 @ X13)
% 0.76/0.98          | ~ (v1_relat_1 @ X13))),
% 0.76/0.98      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.76/0.98  thf(dt_k6_partfun1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( m1_subset_1 @
% 0.76/0.98         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.76/0.98       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.76/0.98  thf('54', plain,
% 0.76/0.98      (![X29 : $i]:
% 0.76/0.98         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 0.76/0.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.76/0.98  thf('55', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.98  thf('56', plain,
% 0.76/0.98      (![X29 : $i]:
% 0.76/0.98         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 0.76/0.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 0.76/0.98      inference('demod', [status(thm)], ['54', '55'])).
% 0.76/0.98  thf('57', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 0.76/0.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.76/0.98          | ~ (v1_relat_1 @ X0)
% 0.76/0.98          | ~ (v1_funct_1 @ X0)
% 0.76/0.98          | ~ (v2_funct_1 @ X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['53', '56'])).
% 0.76/0.98  thf('58', plain,
% 0.76/0.98      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.76/0.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.76/0.98        | ~ (v2_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v1_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v1_relat_1 @ sk_B))),
% 0.76/0.98      inference('sup+', [status(thm)], ['52', '57'])).
% 0.76/0.98  thf('59', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['43', '48', '51'])).
% 0.76/0.98  thf('60', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('61', plain,
% 0.76/0.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.76/0.98         (~ (v1_funct_1 @ X21)
% 0.76/0.98          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.76/0.98          | (v2_funct_1 @ X21)
% 0.76/0.98          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.76/0.98  thf('62', plain,
% 0.76/0.98      (((v2_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.76/0.98        | ~ (v1_funct_1 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['60', '61'])).
% 0.76/0.98  thf('63', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('65', plain, ((v2_funct_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.76/0.98  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.98  thf('68', plain,
% 0.76/0.98      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.76/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('demod', [status(thm)], ['58', '59', '65', '66', '67'])).
% 0.76/0.98  thf('69', plain,
% 0.76/0.98      (![X29 : $i]:
% 0.76/0.98         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 0.76/0.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 0.76/0.98      inference('demod', [status(thm)], ['54', '55'])).
% 0.76/0.98  thf(redefinition_r2_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.98     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.98       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.76/0.98  thf('70', plain,
% 0.76/0.98      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.76/0.98          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.76/0.98          | ((X17) = (X20))
% 0.76/0.98          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.76/0.98  thf('71', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 0.76/0.98          | ((k6_relat_1 @ X0) = (X1))
% 0.76/0.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['69', '70'])).
% 0.76/0.98  thf('72', plain,
% 0.76/0.98      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 0.76/0.98        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.76/0.98             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['68', '71'])).
% 0.76/0.98  thf('73', plain,
% 0.76/0.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.76/0.98           (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.76/0.98        | ~ (v1_relat_1 @ sk_B)
% 0.76/0.98        | ~ (v1_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v2_funct_1 @ sk_B)
% 0.76/0.98        | ((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['35', '72'])).
% 0.76/0.98  thf('74', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['43', '48', '51'])).
% 0.76/0.98  thf('75', plain,
% 0.76/0.98      (![X29 : $i]:
% 0.76/0.98         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 0.76/0.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 0.76/0.98      inference('demod', [status(thm)], ['54', '55'])).
% 0.76/0.98  thf('76', plain,
% 0.76/0.98      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.76/0.98          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.76/0.98          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 0.76/0.98          | ((X17) != (X20)))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.76/0.98  thf('77', plain,
% 0.76/0.98      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.76/0.98         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.76/0.98          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.76/0.98      inference('simplify', [status(thm)], ['76'])).
% 0.76/0.98  thf('78', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['75', '77'])).
% 0.76/0.98  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.98  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('81', plain, ((v2_funct_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.76/0.98  thf('82', plain,
% 0.76/0.98      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['73', '74', '78', '79', '80', '81'])).
% 0.76/0.98  thf('83', plain,
% 0.76/0.98      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.76/0.98         = (k6_relat_1 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['33', '34', '82'])).
% 0.76/0.98  thf('84', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.76/0.98  thf('85', plain,
% 0.76/0.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.76/0.98            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.76/0.98           (k6_partfun1 @ sk_A)))
% 0.76/0.98         <= (~
% 0.76/0.98             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.76/0.98                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.76/0.98               (k6_partfun1 @ sk_A))))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf('86', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.98  thf('87', plain,
% 0.76/0.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.76/0.98            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.76/0.98           (k6_relat_1 @ sk_A)))
% 0.76/0.98         <= (~
% 0.76/0.98             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.76/0.98                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.76/0.98               (k6_partfun1 @ sk_A))))),
% 0.76/0.98      inference('demod', [status(thm)], ['85', '86'])).
% 0.76/0.98  thf('88', plain,
% 0.76/0.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.76/0.98            sk_B) @ 
% 0.76/0.98           (k6_relat_1 @ sk_A)))
% 0.76/0.98         <= (~
% 0.76/0.98             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.76/0.98                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.76/0.98               (k6_partfun1 @ sk_A))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['84', '87'])).
% 0.76/0.98  thf('89', plain,
% 0.76/0.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.76/0.98           (k6_relat_1 @ sk_A)))
% 0.76/0.98         <= (~
% 0.76/0.98             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.76/0.98                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.76/0.98               (k6_partfun1 @ sk_A))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['83', '88'])).
% 0.76/0.98  thf('90', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['75', '77'])).
% 0.76/0.98  thf('91', plain,
% 0.76/0.98      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.76/0.98          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.76/0.98         (k6_partfun1 @ sk_A)))),
% 0.76/0.98      inference('demod', [status(thm)], ['89', '90'])).
% 0.76/0.98  thf('92', plain,
% 0.76/0.98      (~
% 0.76/0.98       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.76/0.98          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.76/0.98         (k6_partfun1 @ sk_A))) | 
% 0.76/0.98       ~
% 0.76/0.98       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.76/0.98          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.76/0.98         (k6_partfun1 @ sk_A)))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf('93', plain,
% 0.76/0.98      (~
% 0.76/0.98       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.76/0.98          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.76/0.98         (k6_partfun1 @ sk_A)))),
% 0.76/0.98      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 0.76/0.98  thf('94', plain,
% 0.76/0.98      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.98          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.76/0.98          (k6_relat_1 @ sk_A))),
% 0.76/0.98      inference('simpl_trail', [status(thm)], ['11', '93'])).
% 0.76/0.98  thf('95', plain,
% 0.76/0.98      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.76/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.76/0.98  thf('96', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('97', plain,
% 0.76/0.98      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.76/0.98          | ~ (v1_funct_1 @ X30)
% 0.76/0.98          | ~ (v1_funct_1 @ X33)
% 0.76/0.98          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.76/0.98          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 0.76/0.98              = (k5_relat_1 @ X30 @ X33)))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.76/0.98  thf('98', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.76/0.98            = (k5_relat_1 @ sk_B @ X0))
% 0.76/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.76/0.98          | ~ (v1_funct_1 @ X0)
% 0.76/0.98          | ~ (v1_funct_1 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['96', '97'])).
% 0.76/0.98  thf('99', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('100', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.76/0.98            = (k5_relat_1 @ sk_B @ X0))
% 0.76/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.76/0.98          | ~ (v1_funct_1 @ X0))),
% 0.76/0.98      inference('demod', [status(thm)], ['98', '99'])).
% 0.76/0.98  thf('101', plain,
% 0.76/0.98      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.76/0.98        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.76/0.98            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['95', '100'])).
% 0.76/0.98  thf('102', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['29', '30'])).
% 0.76/0.98  thf('103', plain,
% 0.76/0.98      (![X13 : $i]:
% 0.76/0.98         (~ (v2_funct_1 @ X13)
% 0.76/0.98          | ((k5_relat_1 @ X13 @ (k2_funct_1 @ X13))
% 0.76/0.98              = (k6_relat_1 @ (k1_relat_1 @ X13)))
% 0.76/0.98          | ~ (v1_funct_1 @ X13)
% 0.76/0.98          | ~ (v1_relat_1 @ X13))),
% 0.76/0.98      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.76/0.98  thf('104', plain,
% 0.76/0.98      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.76/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.76/0.98  thf('105', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.98         ((v4_relat_1 @ X14 @ X15)
% 0.76/0.98          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.98  thf('106', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.76/0.98      inference('sup-', [status(thm)], ['104', '105'])).
% 0.76/0.98  thf(t209_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.76/0.98       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.76/0.98  thf('107', plain,
% 0.76/0.98      (![X9 : $i, X10 : $i]:
% 0.76/0.98         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.76/0.98          | ~ (v4_relat_1 @ X9 @ X10)
% 0.76/0.98          | ~ (v1_relat_1 @ X9))),
% 0.76/0.98      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.76/0.98  thf('108', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.76/0.98        | ((k2_funct_1 @ sk_B) = (k7_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['106', '107'])).
% 0.76/0.98  thf('109', plain,
% 0.76/0.98      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.76/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.76/0.98  thf('110', plain,
% 0.76/0.98      (![X3 : $i, X4 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.76/0.98          | (v1_relat_1 @ X3)
% 0.76/0.98          | ~ (v1_relat_1 @ X4))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.98  thf('111', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.76/0.98        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['109', '110'])).
% 0.76/0.98  thf('112', plain,
% 0.76/0.98      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('113', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['111', '112'])).
% 0.76/0.98  thf('114', plain,
% 0.76/0.98      (((k2_funct_1 @ sk_B) = (k7_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['108', '113'])).
% 0.76/0.98  thf(t148_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ B ) =>
% 0.76/0.98       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.76/0.98  thf('115', plain,
% 0.76/0.98      (![X7 : $i, X8 : $i]:
% 0.76/0.98         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.76/0.98          | ~ (v1_relat_1 @ X7))),
% 0.76/0.98      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.76/0.98  thf('116', plain,
% 0.76/0.98      ((((k2_relat_1 @ (k2_funct_1 @ sk_B))
% 0.76/0.98          = (k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 0.76/0.98        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['114', '115'])).
% 0.76/0.98  thf('117', plain,
% 0.76/0.98      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.76/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.76/0.98  thf('118', plain,
% 0.76/0.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.76/0.98         (~ (v1_funct_1 @ X21)
% 0.76/0.98          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.76/0.98          | (v2_funct_2 @ X21 @ X23)
% 0.76/0.98          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.76/0.98  thf('119', plain,
% 0.76/0.98      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.76/0.98        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.76/0.98        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['117', '118'])).
% 0.76/0.98  thf('120', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('121', plain,
% 0.76/0.98      (![X26 : $i, X27 : $i]:
% 0.76/0.98         ((v3_funct_2 @ (k2_funct_2 @ X26 @ X27) @ X26 @ X26)
% 0.76/0.98          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))
% 0.76/0.98          | ~ (v3_funct_2 @ X27 @ X26 @ X26)
% 0.76/0.98          | ~ (v1_funct_2 @ X27 @ X26 @ X26)
% 0.76/0.98          | ~ (v1_funct_1 @ X27))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.76/0.98  thf('122', plain,
% 0.76/0.98      ((~ (v1_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.76/0.98        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.76/0.98        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['120', '121'])).
% 0.76/0.98  thf('123', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('124', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('125', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('126', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.76/0.98  thf('127', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.76/0.98      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.76/0.98  thf('128', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['29', '30'])).
% 0.76/0.98  thf('129', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.76/0.98      inference('demod', [status(thm)], ['119', '127', '128'])).
% 0.76/0.98  thf('130', plain,
% 0.76/0.98      (![X24 : $i, X25 : $i]:
% 0.76/0.98         (~ (v2_funct_2 @ X25 @ X24)
% 0.76/0.98          | ((k2_relat_1 @ X25) = (X24))
% 0.76/0.98          | ~ (v5_relat_1 @ X25 @ X24)
% 0.76/0.98          | ~ (v1_relat_1 @ X25))),
% 0.76/0.98      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.76/0.98  thf('131', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.76/0.98        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.76/0.98        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['129', '130'])).
% 0.76/0.98  thf('132', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['111', '112'])).
% 0.76/0.98  thf('133', plain,
% 0.76/0.98      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.76/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.76/0.98  thf('134', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.98         ((v5_relat_1 @ X14 @ X16)
% 0.76/0.98          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.98  thf('135', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.76/0.98      inference('sup-', [status(thm)], ['133', '134'])).
% 0.76/0.98  thf('136', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['131', '132', '135'])).
% 0.76/0.98  thf('137', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['43', '48', '51'])).
% 0.76/0.98  thf(t3_funct_2, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.98       ( ( v1_funct_1 @ A ) & 
% 0.76/0.98         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.76/0.98         ( m1_subset_1 @
% 0.76/0.98           A @ 
% 0.76/0.98           ( k1_zfmisc_1 @
% 0.76/0.98             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.76/0.98  thf('138', plain,
% 0.76/0.98      (![X39 : $i]:
% 0.76/0.98         ((m1_subset_1 @ X39 @ 
% 0.76/0.98           (k1_zfmisc_1 @ 
% 0.76/0.98            (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))))
% 0.76/0.98          | ~ (v1_funct_1 @ X39)
% 0.76/0.98          | ~ (v1_relat_1 @ X39))),
% 0.76/0.98      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.76/0.98  thf('139', plain,
% 0.76/0.98      (((m1_subset_1 @ sk_B @ 
% 0.76/0.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.76/0.98        | ~ (v1_relat_1 @ sk_B)
% 0.76/0.98        | ~ (v1_funct_1 @ sk_B))),
% 0.76/0.98      inference('sup+', [status(thm)], ['137', '138'])).
% 0.76/0.98  thf('140', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.98  thf('141', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('142', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_B @ 
% 0.76/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.76/0.98      inference('demod', [status(thm)], ['139', '140', '141'])).
% 0.76/0.98  thf('143', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.98         ((v4_relat_1 @ X14 @ X15)
% 0.76/0.98          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.98  thf('144', plain, ((v4_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['142', '143'])).
% 0.76/0.98  thf('145', plain,
% 0.76/0.98      (![X9 : $i, X10 : $i]:
% 0.76/0.98         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.76/0.98          | ~ (v4_relat_1 @ X9 @ X10)
% 0.76/0.98          | ~ (v1_relat_1 @ X9))),
% 0.76/0.98      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.76/0.98  thf('146', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ sk_B)
% 0.76/0.98        | ((sk_B) = (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['144', '145'])).
% 0.76/0.98  thf('147', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.98  thf('148', plain, (((sk_B) = (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 0.76/0.98      inference('demod', [status(thm)], ['146', '147'])).
% 0.76/0.98  thf('149', plain,
% 0.76/0.98      (![X7 : $i, X8 : $i]:
% 0.76/0.98         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.76/0.98          | ~ (v1_relat_1 @ X7))),
% 0.76/0.98      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.76/0.98  thf('150', plain,
% 0.76/0.98      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.76/0.98        | ~ (v1_relat_1 @ sk_B))),
% 0.76/0.98      inference('sup+', [status(thm)], ['148', '149'])).
% 0.76/0.98  thf('151', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['43', '48', '51'])).
% 0.76/0.98  thf('152', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.98  thf('153', plain, (((sk_A) = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 0.76/0.98      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.76/0.98  thf(d10_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.98  thf('154', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.76/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.98  thf('155', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.76/0.98      inference('simplify', [status(thm)], ['154'])).
% 0.76/0.98  thf(t177_funct_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.76/0.98           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.76/0.98             ( B ) ) ) ) ))).
% 0.76/0.98  thf('156', plain,
% 0.76/0.98      (![X11 : $i, X12 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 0.76/0.98          | ((k9_relat_1 @ (k2_funct_1 @ X12) @ (k9_relat_1 @ X12 @ X11))
% 0.76/0.98              = (X11))
% 0.76/0.98          | ~ (v2_funct_1 @ X12)
% 0.76/0.98          | ~ (v1_funct_1 @ X12)
% 0.76/0.98          | ~ (v1_relat_1 @ X12))),
% 0.76/0.98      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.76/0.98  thf('157', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ X0)
% 0.76/0.98          | ~ (v1_funct_1 @ X0)
% 0.76/0.98          | ~ (v2_funct_1 @ X0)
% 0.76/0.98          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.76/0.98              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['155', '156'])).
% 0.76/0.98  thf('158', plain,
% 0.76/0.98      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))
% 0.76/0.98        | ~ (v2_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v1_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v1_relat_1 @ sk_B))),
% 0.76/0.98      inference('sup+', [status(thm)], ['153', '157'])).
% 0.76/0.98  thf('159', plain, ((v2_funct_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.76/0.98  thf('160', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('161', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.98  thf('162', plain,
% 0.76/0.98      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['158', '159', '160', '161'])).
% 0.76/0.98  thf('163', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['111', '112'])).
% 0.76/0.98  thf('164', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['116', '136', '162', '163'])).
% 0.76/0.98  thf('165', plain,
% 0.76/0.98      (![X13 : $i]:
% 0.76/0.98         (~ (v2_funct_1 @ X13)
% 0.76/0.98          | ((k5_relat_1 @ X13 @ (k2_funct_1 @ X13))
% 0.76/0.98              = (k6_relat_1 @ (k1_relat_1 @ X13)))
% 0.76/0.98          | ~ (v1_funct_1 @ X13)
% 0.76/0.98          | ~ (v1_relat_1 @ X13))),
% 0.76/0.98      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.76/0.98  thf('166', plain,
% 0.76/0.98      (![X29 : $i]:
% 0.76/0.98         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 0.76/0.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 0.76/0.98      inference('demod', [status(thm)], ['54', '55'])).
% 0.76/0.98  thf('167', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 0.76/0.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.76/0.98          | ~ (v1_relat_1 @ X0)
% 0.76/0.98          | ~ (v1_funct_1 @ X0)
% 0.76/0.98          | ~ (v2_funct_1 @ X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['165', '166'])).
% 0.76/0.98  thf('168', plain,
% 0.76/0.98      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.76/0.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.76/0.98        | ~ (v2_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v1_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v1_relat_1 @ sk_B))),
% 0.76/0.98      inference('sup+', [status(thm)], ['164', '167'])).
% 0.76/0.98  thf('169', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['116', '136', '162', '163'])).
% 0.76/0.98  thf('170', plain, ((v2_funct_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.76/0.98  thf('171', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('172', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.98  thf('173', plain,
% 0.76/0.98      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.76/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('demod', [status(thm)], ['168', '169', '170', '171', '172'])).
% 0.76/0.98  thf('174', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 0.76/0.98          | ((k6_relat_1 @ X0) = (X1))
% 0.76/0.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['69', '70'])).
% 0.76/0.98  thf('175', plain,
% 0.76/0.98      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 0.76/0.98        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.76/0.98             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['173', '174'])).
% 0.76/0.98  thf('176', plain,
% 0.76/0.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.76/0.98           (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.76/0.98        | ~ (v1_relat_1 @ sk_B)
% 0.76/0.98        | ~ (v1_funct_1 @ sk_B)
% 0.76/0.98        | ~ (v2_funct_1 @ sk_B)
% 0.76/0.98        | ((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['103', '175'])).
% 0.76/0.98  thf('177', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['116', '136', '162', '163'])).
% 0.76/0.98  thf('178', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['75', '77'])).
% 0.76/0.98  thf('179', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.98  thf('180', plain, ((v1_funct_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('181', plain, ((v2_funct_1 @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.76/0.98  thf('182', plain,
% 0.76/0.98      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 0.76/0.98      inference('demod', [status(thm)],
% 0.76/0.98                ['176', '177', '178', '179', '180', '181'])).
% 0.76/0.98  thf('183', plain,
% 0.76/0.98      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.76/0.98         = (k6_relat_1 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['101', '102', '182'])).
% 0.76/0.98  thf('184', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['75', '77'])).
% 0.76/0.98  thf('185', plain, ($false),
% 0.76/0.98      inference('demod', [status(thm)], ['94', '183', '184'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
