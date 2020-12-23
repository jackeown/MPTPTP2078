%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NWUzCGKpRy

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:25 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  214 (7441 expanded)
%              Number of leaves         :   42 (2233 expanded)
%              Depth                    :   23
%              Number of atoms          : 1630 (141620 expanded)
%              Number of equality atoms :  131 (7197 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t92_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ A )
        & ( v3_funct_2 @ C @ A @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r1_tarski @ B @ A )
       => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
            = B )
          & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
            = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ A )
          & ( v3_funct_2 @ C @ A @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r1_tarski @ B @ A )
         => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
              = B )
            & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
              = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t92_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('11',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('12',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v3_funct_2 @ X37 @ X38 @ X39 )
      | ( v2_funct_2 @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('17',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('21',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v2_funct_2 @ X41 @ X40 )
      | ( ( k2_relat_1 @ X41 )
        = X40 )
      | ~ ( v5_relat_1 @ X41 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','28'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['14','34'])).

thf('36',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['12','13','35'])).

thf('37',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('39',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['9','39'])).

thf('41',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('46',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X45 ) ) )
      | ( ( k8_relset_1 @ X43 @ X45 @ X44 @ X45 )
        = X43 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('47',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A )
      = sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_A )
      = sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','28'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X42: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X45 ) ) )
      | ( ( k8_relset_1 @ X43 @ X45 @ X44 @ X45 )
        = X43 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('59',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('61',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','28'])).

thf('64',plain,(
    ! [X42: $i] :
      ( ( v1_funct_2 @ X42 @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('65',plain,
    ( ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62','68','69'])).

thf('71',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('73',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ( ( k10_relat_1 @ X13 @ ( k9_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v3_funct_2 @ X37 @ X38 @ X39 )
      | ( v2_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('79',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','82'])).

thf('84',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
      = sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','83'])).

thf('85',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['9','39'])).

thf('86',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('87',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('89',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['43','86','87','88'])).

thf('90',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['43','86','87','88'])).

thf('91',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ k1_xboole_0 ) )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('93',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('94',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('98',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('102',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('105',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('108',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('115',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
       != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('121',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('122',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('124',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['96','97','98','119','120','121','122','123'])).

thf('125',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['96','97','98','119','120','121','122','123'])).

thf('126',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('127',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('130',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('131',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('132',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k8_relset_1 @ X34 @ X35 @ X36 @ ( k7_relset_1 @ X34 @ X35 @ X36 @ X34 ) )
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X1 ) )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('135',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('138',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('141',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('144',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('145',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('149',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('150',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['147','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('153',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['142','153'])).

thf('155',plain,(
    ! [X1: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ ( k9_relat_1 @ k1_xboole_0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['133','136','139','154'])).

thf('156',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['128','155'])).

thf('157',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['148','149'])).

thf('158',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['96','97','98','119','120','121','122','123'])).

thf('161',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['158','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('164',plain,
    ( ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['159','160'])).

thf('166',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['148','149'])).

thf('167',plain,
    ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,
    ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['158','161'])).

thf('169',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['91','124','125','167','168'])).

thf('170',plain,(
    $false ),
    inference(simplify,[status(thm)],['169'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NWUzCGKpRy
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:08:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 289 iterations in 0.127s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.55  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.19/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.55  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.19/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.55  thf(t92_funct_2, conjecture,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.19/0.55         ( v3_funct_2 @ C @ A @ A ) & 
% 0.19/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.55       ( ( r1_tarski @ B @ A ) =>
% 0.19/0.55         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.19/0.55             ( B ) ) & 
% 0.19/0.55           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.19/0.55             ( B ) ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.19/0.55            ( v3_funct_2 @ C @ A @ A ) & 
% 0.19/0.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.55          ( ( r1_tarski @ B @ A ) =>
% 0.19/0.55            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.19/0.55                ( B ) ) & 
% 0.19/0.55              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.19/0.55                ( B ) ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.19/0.55  thf('0', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(redefinition_k8_relset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.19/0.55          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 0.19/0.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.55  thf('4', plain,
% 0.19/0.55      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.19/0.55          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 0.19/0.55      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.19/0.55        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.19/0.55         <= (~
% 0.19/0.55             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.19/0.55      inference('split', [status(esa)], ['6'])).
% 0.19/0.55  thf('8', plain,
% 0.19/0.55      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.19/0.55          != (sk_B)))
% 0.19/0.55         <= (~
% 0.19/0.55             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['5', '7'])).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.19/0.55         <= (~
% 0.19/0.55             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['2', '8'])).
% 0.19/0.55  thf('10', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.55  thf('11', plain,
% 0.19/0.55      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.19/0.55         <= (~
% 0.19/0.55             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.19/0.55      inference('split', [status(esa)], ['6'])).
% 0.19/0.55  thf('12', plain,
% 0.19/0.55      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_B))
% 0.19/0.55          != (sk_B)))
% 0.19/0.55         <= (~
% 0.19/0.55             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.55  thf('14', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(cc2_funct_2, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.19/0.55         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.19/0.55         (~ (v1_funct_1 @ X37)
% 0.19/0.55          | ~ (v3_funct_2 @ X37 @ X38 @ X39)
% 0.19/0.55          | (v2_funct_2 @ X37 @ X39)
% 0.19/0.55          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.19/0.55      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.19/0.55  thf('17', plain,
% 0.19/0.55      (((v2_funct_2 @ sk_C @ sk_A)
% 0.19/0.55        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.19/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.19/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.55  thf('18', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('20', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.19/0.55      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.19/0.55  thf(d3_funct_2, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.19/0.55       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.19/0.55  thf('21', plain,
% 0.19/0.55      (![X40 : $i, X41 : $i]:
% 0.19/0.55         (~ (v2_funct_2 @ X41 @ X40)
% 0.19/0.55          | ((k2_relat_1 @ X41) = (X40))
% 0.19/0.55          | ~ (v5_relat_1 @ X41 @ X40)
% 0.19/0.55          | ~ (v1_relat_1 @ X41))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.55        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.19/0.55        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(cc1_relset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( v1_relat_1 @ C ) ))).
% 0.19/0.55  thf('24', plain,
% 0.19/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.55         ((v1_relat_1 @ X14)
% 0.19/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.19/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.55  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(cc2_relset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.55  thf('27', plain,
% 0.19/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.55         ((v5_relat_1 @ X17 @ X19)
% 0.19/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.19/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.55  thf('28', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.19/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.55  thf('29', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['22', '25', '28'])).
% 0.19/0.55  thf(t147_funct_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.55       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.19/0.55         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.19/0.55  thf('30', plain,
% 0.19/0.55      (![X10 : $i, X11 : $i]:
% 0.19/0.55         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 0.19/0.55          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 0.19/0.55          | ~ (v1_funct_1 @ X11)
% 0.19/0.55          | ~ (v1_relat_1 @ X11))),
% 0.19/0.55      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.19/0.55  thf('31', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (r1_tarski @ X0 @ sk_A)
% 0.19/0.55          | ~ (v1_relat_1 @ sk_C)
% 0.19/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.19/0.55          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.55  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.55  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('34', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (r1_tarski @ X0 @ sk_A)
% 0.19/0.55          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.19/0.55  thf('35', plain,
% 0.19/0.55      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['14', '34'])).
% 0.19/0.55  thf('36', plain,
% 0.19/0.55      ((((sk_B) != (sk_B)))
% 0.19/0.55         <= (~
% 0.19/0.55             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.19/0.55      inference('demod', [status(thm)], ['12', '13', '35'])).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.19/0.55  thf('38', plain,
% 0.19/0.55      (~
% 0.19/0.55       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.19/0.55       ~
% 0.19/0.55       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.19/0.55      inference('split', [status(esa)], ['6'])).
% 0.19/0.55  thf('39', plain,
% 0.19/0.55      (~
% 0.19/0.55       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.19/0.55          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.19/0.55  thf('40', plain,
% 0.19/0.55      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['9', '39'])).
% 0.19/0.55  thf('41', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d10_xboole_0, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.55  thf('42', plain,
% 0.19/0.55      (![X0 : $i, X2 : $i]:
% 0.19/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.55  thf('43', plain, ((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.55  thf('44', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('45', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t48_funct_2, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.55         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.19/0.55  thf('46', plain,
% 0.19/0.55      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.19/0.55         (((X45) = (k1_xboole_0))
% 0.19/0.55          | ~ (v1_funct_1 @ X44)
% 0.19/0.55          | ~ (v1_funct_2 @ X44 @ X43 @ X45)
% 0.19/0.55          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X45)))
% 0.19/0.55          | ((k8_relset_1 @ X43 @ X45 @ X44 @ X45) = (X43)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.19/0.55  thf('47', plain,
% 0.19/0.55      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A) = (sk_A))
% 0.19/0.55        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.19/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.55  thf('48', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.55  thf('49', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('51', plain,
% 0.19/0.55      ((((k10_relat_1 @ sk_C @ sk_A) = (sk_A)) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.19/0.55  thf('52', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['22', '25', '28'])).
% 0.19/0.55  thf(t3_funct_2, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.55       ( ( v1_funct_1 @ A ) & 
% 0.19/0.55         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.19/0.55         ( m1_subset_1 @
% 0.19/0.55           A @ 
% 0.19/0.55           ( k1_zfmisc_1 @
% 0.19/0.55             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.55  thf('53', plain,
% 0.19/0.55      (![X42 : $i]:
% 0.19/0.55         ((m1_subset_1 @ X42 @ 
% 0.19/0.55           (k1_zfmisc_1 @ 
% 0.19/0.55            (k2_zfmisc_1 @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42))))
% 0.19/0.55          | ~ (v1_funct_1 @ X42)
% 0.19/0.55          | ~ (v1_relat_1 @ X42))),
% 0.19/0.55      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.19/0.55  thf('54', plain,
% 0.19/0.55      (((m1_subset_1 @ sk_C @ 
% 0.19/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))
% 0.19/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.19/0.55      inference('sup+', [status(thm)], ['52', '53'])).
% 0.19/0.55  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.55  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('57', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.19/0.55      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.19/0.55  thf('58', plain,
% 0.19/0.55      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.19/0.55         (((X45) = (k1_xboole_0))
% 0.19/0.55          | ~ (v1_funct_1 @ X44)
% 0.19/0.55          | ~ (v1_funct_2 @ X44 @ X43 @ X45)
% 0.19/0.55          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X45)))
% 0.19/0.55          | ((k8_relset_1 @ X43 @ X45 @ X44 @ X45) = (X43)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.19/0.55  thf('59', plain,
% 0.19/0.55      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ sk_A)
% 0.19/0.55          = (k1_relat_1 @ sk_C))
% 0.19/0.55        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_A)
% 0.19/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.55  thf('60', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.19/0.55      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.19/0.55  thf('61', plain,
% 0.19/0.55      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.19/0.55          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 0.19/0.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.55  thf('62', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0)
% 0.19/0.55           = (k10_relat_1 @ sk_C @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.55  thf('63', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['22', '25', '28'])).
% 0.19/0.55  thf('64', plain,
% 0.19/0.55      (![X42 : $i]:
% 0.19/0.55         ((v1_funct_2 @ X42 @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42))
% 0.19/0.55          | ~ (v1_funct_1 @ X42)
% 0.19/0.55          | ~ (v1_relat_1 @ X42))),
% 0.19/0.55      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.19/0.55  thf('65', plain,
% 0.19/0.55      (((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_A)
% 0.19/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.19/0.55      inference('sup+', [status(thm)], ['63', '64'])).
% 0.19/0.55  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.55  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('68', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.19/0.55      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.19/0.55  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('70', plain,
% 0.19/0.55      ((((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['59', '62', '68', '69'])).
% 0.19/0.55  thf('71', plain,
% 0.19/0.55      ((((sk_A) = (k1_relat_1 @ sk_C))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['51', '70'])).
% 0.19/0.55  thf('72', plain,
% 0.19/0.55      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.19/0.55  thf(t164_funct_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.55       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.19/0.55         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.19/0.55  thf('73', plain,
% 0.19/0.55      (![X12 : $i, X13 : $i]:
% 0.19/0.55         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 0.19/0.55          | ~ (v2_funct_1 @ X13)
% 0.19/0.55          | ((k10_relat_1 @ X13 @ (k9_relat_1 @ X13 @ X12)) = (X12))
% 0.19/0.55          | ~ (v1_funct_1 @ X13)
% 0.19/0.55          | ~ (v1_relat_1 @ X13))),
% 0.19/0.55      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.19/0.55  thf('74', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (r1_tarski @ X0 @ sk_A)
% 0.19/0.55          | ((sk_A) = (k1_xboole_0))
% 0.19/0.55          | ~ (v1_relat_1 @ sk_C)
% 0.19/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.19/0.55          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.19/0.55          | ~ (v2_funct_1 @ sk_C))),
% 0.19/0.55      inference('sup-', [status(thm)], ['72', '73'])).
% 0.19/0.55  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.55  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('77', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('78', plain,
% 0.19/0.55      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.19/0.55         (~ (v1_funct_1 @ X37)
% 0.19/0.55          | ~ (v3_funct_2 @ X37 @ X38 @ X39)
% 0.19/0.55          | (v2_funct_1 @ X37)
% 0.19/0.55          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.19/0.55      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.19/0.55  thf('79', plain,
% 0.19/0.55      (((v2_funct_1 @ sk_C)
% 0.19/0.55        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.19/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.19/0.55      inference('sup-', [status(thm)], ['77', '78'])).
% 0.19/0.55  thf('80', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.55      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.19/0.55  thf('83', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (r1_tarski @ X0 @ sk_A)
% 0.19/0.55          | ((sk_A) = (k1_xboole_0))
% 0.19/0.55          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['74', '75', '76', '82'])).
% 0.19/0.55  thf('84', plain,
% 0.19/0.55      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['44', '83'])).
% 0.19/0.55  thf('85', plain,
% 0.19/0.55      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['9', '39'])).
% 0.19/0.55  thf('86', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.56      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.19/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.56  thf('87', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.19/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.56  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.56      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.19/0.56  thf('89', plain, (((k1_xboole_0) = (sk_B))),
% 0.19/0.56      inference('demod', [status(thm)], ['43', '86', '87', '88'])).
% 0.19/0.56  thf('90', plain, (((k1_xboole_0) = (sk_B))),
% 0.19/0.56      inference('demod', [status(thm)], ['43', '86', '87', '88'])).
% 0.19/0.56  thf('91', plain,
% 0.19/0.56      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ k1_xboole_0))
% 0.19/0.56         != (k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['40', '89', '90'])).
% 0.19/0.56  thf('92', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(t3_subset, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.56  thf('93', plain,
% 0.19/0.56      (![X4 : $i, X5 : $i]:
% 0.19/0.56         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.56  thf('94', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.19/0.56      inference('sup-', [status(thm)], ['92', '93'])).
% 0.19/0.56  thf('95', plain,
% 0.19/0.56      (![X0 : $i, X2 : $i]:
% 0.19/0.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.56  thf('96', plain,
% 0.19/0.56      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_C)
% 0.19/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_C)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['94', '95'])).
% 0.19/0.56  thf('97', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.56      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.19/0.56  thf('98', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.56      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.19/0.56  thf('99', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.56  thf('100', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.56      inference('simplify', [status(thm)], ['99'])).
% 0.19/0.56  thf('101', plain,
% 0.19/0.56      (![X4 : $i, X6 : $i]:
% 0.19/0.56         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.19/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.56  thf('102', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['100', '101'])).
% 0.19/0.56  thf('103', plain,
% 0.19/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.56         ((v4_relat_1 @ X17 @ X18)
% 0.19/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.19/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.56  thf('104', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 0.19/0.56      inference('sup-', [status(thm)], ['102', '103'])).
% 0.19/0.56  thf(d18_relat_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( v1_relat_1 @ B ) =>
% 0.19/0.56       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.56  thf('105', plain,
% 0.19/0.56      (![X7 : $i, X8 : $i]:
% 0.19/0.56         (~ (v4_relat_1 @ X7 @ X8)
% 0.19/0.56          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.19/0.56          | ~ (v1_relat_1 @ X7))),
% 0.19/0.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.56  thf('106', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 0.19/0.56          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['104', '105'])).
% 0.19/0.56  thf('107', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['100', '101'])).
% 0.19/0.56  thf('108', plain,
% 0.19/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.56         ((v1_relat_1 @ X14)
% 0.19/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.19/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.56  thf('109', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['107', '108'])).
% 0.19/0.56  thf('110', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 0.19/0.56      inference('demod', [status(thm)], ['106', '109'])).
% 0.19/0.56  thf('111', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.19/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.56  thf('112', plain,
% 0.19/0.56      (![X0 : $i, X2 : $i]:
% 0.19/0.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.56  thf('113', plain,
% 0.19/0.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['111', '112'])).
% 0.19/0.56  thf('114', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((k1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['110', '113'])).
% 0.19/0.56  thf(t64_relat_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( v1_relat_1 @ A ) =>
% 0.19/0.56       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.56           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.56         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.56  thf('115', plain,
% 0.19/0.56      (![X9 : $i]:
% 0.19/0.56         (((k1_relat_1 @ X9) != (k1_xboole_0))
% 0.19/0.56          | ((X9) = (k1_xboole_0))
% 0.19/0.56          | ~ (v1_relat_1 @ X9))),
% 0.19/0.56      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.19/0.56  thf('116', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.56          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.19/0.56          | ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['114', '115'])).
% 0.19/0.56  thf('117', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['107', '108'])).
% 0.19/0.56  thf('118', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.56          | ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.19/0.56      inference('demod', [status(thm)], ['116', '117'])).
% 0.19/0.56  thf('119', plain,
% 0.19/0.56      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.56      inference('simplify', [status(thm)], ['118'])).
% 0.19/0.56  thf('120', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.19/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.56  thf('121', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.56      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.19/0.56  thf('122', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.56      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.19/0.56  thf('123', plain,
% 0.19/0.56      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.56      inference('simplify', [status(thm)], ['118'])).
% 0.19/0.56  thf('124', plain, (((k1_xboole_0) = (sk_C))),
% 0.19/0.56      inference('demod', [status(thm)],
% 0.19/0.56                ['96', '97', '98', '119', '120', '121', '122', '123'])).
% 0.19/0.56  thf('125', plain, (((k1_xboole_0) = (sk_C))),
% 0.19/0.56      inference('demod', [status(thm)],
% 0.19/0.56                ['96', '97', '98', '119', '120', '121', '122', '123'])).
% 0.19/0.56  thf('126', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.19/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.56  thf('127', plain,
% 0.19/0.56      (![X10 : $i, X11 : $i]:
% 0.19/0.56         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 0.19/0.56          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 0.19/0.56          | ~ (v1_funct_1 @ X11)
% 0.19/0.56          | ~ (v1_relat_1 @ X11))),
% 0.19/0.56      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.19/0.56  thf('128', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 0.19/0.56              = (k1_xboole_0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['126', '127'])).
% 0.19/0.56  thf('129', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.19/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.56  thf('130', plain,
% 0.19/0.56      (![X4 : $i, X6 : $i]:
% 0.19/0.56         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.19/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.56  thf('131', plain,
% 0.19/0.56      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['129', '130'])).
% 0.19/0.56  thf(t39_relset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.56       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.19/0.56           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.19/0.56         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.19/0.56           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.19/0.56  thf('132', plain,
% 0.19/0.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.19/0.56         (((k8_relset_1 @ X34 @ X35 @ X36 @ 
% 0.19/0.56            (k7_relset_1 @ X34 @ X35 @ X36 @ X34))
% 0.19/0.56            = (k1_relset_1 @ X34 @ X35 @ X36))
% 0.19/0.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.19/0.56      inference('cnf', [status(esa)], [t39_relset_1])).
% 0.19/0.56  thf('133', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ 
% 0.19/0.56           (k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X1))
% 0.19/0.56           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['131', '132'])).
% 0.19/0.56  thf('134', plain,
% 0.19/0.56      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['129', '130'])).
% 0.19/0.56  thf('135', plain,
% 0.19/0.56      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.56         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.19/0.56          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 0.19/0.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.56  thf('136', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.19/0.56           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 0.19/0.56      inference('sup-', [status(thm)], ['134', '135'])).
% 0.19/0.56  thf('137', plain,
% 0.19/0.56      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['129', '130'])).
% 0.19/0.56  thf('138', plain,
% 0.19/0.56      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.19/0.56         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.19/0.56          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 0.19/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.56  thf('139', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.19/0.56           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.19/0.56      inference('sup-', [status(thm)], ['137', '138'])).
% 0.19/0.56  thf('140', plain,
% 0.19/0.56      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['129', '130'])).
% 0.19/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.56  thf('141', plain,
% 0.19/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.56         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.19/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.19/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.56  thf('142', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['140', '141'])).
% 0.19/0.56  thf('143', plain,
% 0.19/0.56      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['129', '130'])).
% 0.19/0.56  thf('144', plain,
% 0.19/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.56         ((v4_relat_1 @ X17 @ X18)
% 0.19/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.19/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.56  thf('145', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.19/0.56      inference('sup-', [status(thm)], ['143', '144'])).
% 0.19/0.56  thf('146', plain,
% 0.19/0.56      (![X7 : $i, X8 : $i]:
% 0.19/0.56         (~ (v4_relat_1 @ X7 @ X8)
% 0.19/0.56          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.19/0.56          | ~ (v1_relat_1 @ X7))),
% 0.19/0.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.56  thf('147', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.56          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['145', '146'])).
% 0.19/0.56  thf('148', plain,
% 0.19/0.56      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['129', '130'])).
% 0.19/0.56  thf('149', plain,
% 0.19/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.56         ((v1_relat_1 @ X14)
% 0.19/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.19/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.56  thf('150', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.56      inference('sup-', [status(thm)], ['148', '149'])).
% 0.19/0.56  thf('151', plain,
% 0.19/0.56      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.19/0.56      inference('demod', [status(thm)], ['147', '150'])).
% 0.19/0.56  thf('152', plain,
% 0.19/0.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['111', '112'])).
% 0.19/0.56  thf('153', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['151', '152'])).
% 0.19/0.56  thf('154', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['142', '153'])).
% 0.19/0.56  thf('155', plain,
% 0.19/0.56      (![X1 : $i]:
% 0.19/0.56         ((k10_relat_1 @ k1_xboole_0 @ (k9_relat_1 @ k1_xboole_0 @ X1))
% 0.19/0.56           = (k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['133', '136', '139', '154'])).
% 0.19/0.56  thf('156', plain,
% 0.19/0.56      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.56        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.56        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.56      inference('sup+', [status(thm)], ['128', '155'])).
% 0.19/0.56  thf('157', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.56      inference('sup-', [status(thm)], ['148', '149'])).
% 0.19/0.56  thf('158', plain,
% 0.19/0.56      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.56        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['156', '157'])).
% 0.19/0.56  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('160', plain, (((k1_xboole_0) = (sk_C))),
% 0.19/0.56      inference('demod', [status(thm)],
% 0.19/0.56                ['96', '97', '98', '119', '120', '121', '122', '123'])).
% 0.19/0.56  thf('161', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.19/0.56      inference('demod', [status(thm)], ['159', '160'])).
% 0.19/0.56  thf('162', plain,
% 0.19/0.56      (((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['158', '161'])).
% 0.19/0.56  thf('163', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 0.19/0.56              = (k1_xboole_0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['126', '127'])).
% 0.19/0.56  thf('164', plain,
% 0.19/0.56      ((((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.56        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.56        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.56      inference('sup+', [status(thm)], ['162', '163'])).
% 0.19/0.56  thf('165', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.19/0.56      inference('demod', [status(thm)], ['159', '160'])).
% 0.19/0.56  thf('166', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.56      inference('sup-', [status(thm)], ['148', '149'])).
% 0.19/0.56  thf('167', plain,
% 0.19/0.56      (((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['164', '165', '166'])).
% 0.19/0.56  thf('168', plain,
% 0.19/0.56      (((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['158', '161'])).
% 0.19/0.56  thf('169', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['91', '124', '125', '167', '168'])).
% 0.19/0.56  thf('170', plain, ($false), inference('simplify', [status(thm)], ['169'])).
% 0.19/0.56  
% 0.19/0.56  % SZS output end Refutation
% 0.19/0.56  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
