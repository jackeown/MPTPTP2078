%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.al4YFdXSdw

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 227 expanded)
%              Number of leaves         :   44 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          : 1029 (3024 expanded)
%              Number of equality atoms :  103 ( 256 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t52_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                  = ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_struct_0 @ B )
                      = k1_xboole_0 )
                   => ( ( k2_struct_0 @ A )
                      = k1_xboole_0 ) )
                 => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ( v1_partfun1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X34 @ X32 )
      | ( v1_partfun1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('9',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('10',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('20',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('26',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('33',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('35',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','42'])).

thf(t171_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf('44',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k8_relset_1 @ X36 @ X36 @ ( k6_partfun1 @ X36 ) @ X35 )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf('45',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_C )
      = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('46',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('47',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('48',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('49',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('50',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k10_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t172_relat_1,axiom,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('52',plain,(
    ! [X13: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','54','55'])).

thf('57',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('59',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','60'])).

thf('62',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k10_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('75',plain,(
    v5_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('76',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('79',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('80',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('81',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('82',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ X18 @ ( k6_partfun1 @ X19 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('85',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['83','84'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('86',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('87',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('89',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('91',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('92',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('95',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['85','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('97',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','68','97'])).

thf('99',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.al4YFdXSdw
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:32:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 236 iterations in 0.084s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(d3_struct_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (![X37 : $i]:
% 0.20/0.54         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X37 : $i]:
% 0.20/0.54         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.54  thf(t52_tops_2, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_struct_0 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( l1_struct_0 @ B ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.54                 ( m1_subset_1 @
% 0.20/0.54                   C @ 
% 0.20/0.54                   ( k1_zfmisc_1 @
% 0.20/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.54               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.54                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.54                 ( ( k8_relset_1 @
% 0.20/0.54                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.54                     ( k2_struct_0 @ B ) ) =
% 0.20/0.54                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( l1_struct_0 @ A ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( l1_struct_0 @ B ) =>
% 0.20/0.54              ( ![C:$i]:
% 0.20/0.54                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.54                    ( v1_funct_2 @
% 0.20/0.54                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.54                    ( m1_subset_1 @
% 0.20/0.54                      C @ 
% 0.20/0.54                      ( k1_zfmisc_1 @
% 0.20/0.54                        ( k2_zfmisc_1 @
% 0.20/0.54                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.54                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.54                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.54                    ( ( k8_relset_1 @
% 0.20/0.54                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.54                        ( k2_struct_0 @ B ) ) =
% 0.20/0.54                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t132_funct_2, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.54       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.54           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.54           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.54         (((X32) = (k1_xboole_0))
% 0.20/0.54          | ~ (v1_funct_1 @ X33)
% 0.20/0.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 0.20/0.54          | (v1_partfun1 @ X33 @ X34)
% 0.20/0.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 0.20/0.54          | ~ (v1_funct_2 @ X33 @ X34 @ X32)
% 0.20/0.54          | ~ (v1_funct_1 @ X33))),
% 0.20/0.54      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.54         (~ (v1_funct_2 @ X33 @ X34 @ X32)
% 0.20/0.54          | (v1_partfun1 @ X33 @ X34)
% 0.20/0.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 0.20/0.54          | ~ (v1_funct_1 @ X33)
% 0.20/0.54          | ((X32) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.54        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.54  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.54        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.54  thf(d4_partfun1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.54       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X29 : $i, X30 : $i]:
% 0.20/0.54         (~ (v1_partfun1 @ X30 @ X29)
% 0.20/0.54          | ((k1_relat_1 @ X30) = (X29))
% 0.20/0.54          | ~ (v4_relat_1 @ X30 @ X29)
% 0.20/0.54          | ~ (v1_relat_1 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc2_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.20/0.54          | (v1_relat_1 @ X7)
% 0.20/0.54          | ~ (v1_relat_1 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ 
% 0.20/0.54           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.20/0.54        | (v1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.54  thf(fc6_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.54  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc2_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.54         ((v4_relat_1 @ X22 @ X23)
% 0.20/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.54  thf('18', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.54        | ~ (l1_struct_0 @ sk_B)
% 0.20/0.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '19'])).
% 0.20/0.54  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.20/0.54         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.20/0.54      inference('split', [status(esa)], ['23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.20/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.54      inference('split', [status(esa)], ['23'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X37 : $i]:
% 0.20/0.54         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.54         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.54          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.20/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.54         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.54          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.20/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['25', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.20/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.54      inference('split', [status(esa)], ['23'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.54          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.20/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.54      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.20/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.54      inference('split', [status(esa)], ['23'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X37 : $i]:
% 0.20/0.54         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_C @ 
% 0.20/0.54         (k1_zfmisc_1 @ 
% 0.20/0.54          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.20/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.54  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_C @ 
% 0.20/0.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.20/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['34', '39'])).
% 0.20/0.54  thf(t113_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.20/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.54      inference('demod', [status(thm)], ['40', '42'])).
% 0.20/0.54  thf(t171_funct_2, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (![X35 : $i, X36 : $i]:
% 0.20/0.54         (((k8_relset_1 @ X36 @ X36 @ (k6_partfun1 @ X36) @ X35) = (X35))
% 0.20/0.54          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t171_funct_2])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      ((((k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.54          (k6_partfun1 @ k1_xboole_0) @ sk_C) = (sk_C)))
% 0.20/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.54  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.54  thf('46', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.54  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.54  thf('47', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.54  thf('48', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.54  thf(t4_subset_1, axiom,
% 0.20/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.54  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.20/0.54          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.20/0.54           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.20/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf(t172_relat_1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (![X13 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t172_relat_1])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      ((((k1_xboole_0) = (sk_C))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.54      inference('demod', [status(thm)], ['45', '48', '53'])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.54      inference('demod', [status(thm)], ['33', '54', '55'])).
% 0.20/0.54  thf('57', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.20/0.54       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('split', [status(esa)], ['23'])).
% 0.20/0.54  thf('59', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['24', '59'])).
% 0.20/0.54  thf('61', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['22', '60'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup+', [status(thm)], ['0', '61'])).
% 0.20/0.54  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('64', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.54         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.20/0.54          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.54           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      (![X37 : $i]:
% 0.20/0.54         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.54  thf('70', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_C @ 
% 0.20/0.54         (k1_zfmisc_1 @ 
% 0.20/0.54          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.20/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.54  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.20/0.54      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.54         ((v5_relat_1 @ X22 @ X24)
% 0.20/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.54  thf('75', plain, ((v5_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.54  thf(d19_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (~ (v5_relat_1 @ X9 @ X10)
% 0.20/0.54          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.20/0.54          | ~ (v1_relat_1 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.54  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('79', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.54  thf(t79_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.54         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.20/0.54  thf('80', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.20/0.54          | ((k5_relat_1 @ X18 @ (k6_relat_1 @ X19)) = (X18))
% 0.20/0.54          | ~ (v1_relat_1 @ X18))),
% 0.20/0.54      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.20/0.54  thf('81', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.20/0.54          | ((k5_relat_1 @ X18 @ (k6_partfun1 @ X19)) = (X18))
% 0.20/0.54          | ~ (v1_relat_1 @ X18))),
% 0.20/0.54      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.54  thf('83', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | ((k5_relat_1 @ sk_C @ (k6_partfun1 @ (k2_struct_0 @ sk_B))) = (sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['79', '82'])).
% 0.20/0.54  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('85', plain,
% 0.20/0.54      (((k5_relat_1 @ sk_C @ (k6_partfun1 @ (k2_struct_0 @ sk_B))) = (sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['83', '84'])).
% 0.20/0.54  thf(t71_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.54  thf('86', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.20/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.54  thf('87', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.54  thf('88', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 0.20/0.54      inference('demod', [status(thm)], ['86', '87'])).
% 0.20/0.54  thf(t182_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( v1_relat_1 @ B ) =>
% 0.20/0.54           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.54             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.54  thf('89', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X14)
% 0.20/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 0.20/0.54              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 0.20/0.54          | ~ (v1_relat_1 @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.54  thf('90', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.20/0.54            = (k10_relat_1 @ X1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X1)
% 0.20/0.54          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['88', '89'])).
% 0.20/0.54  thf(fc4_funct_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.54  thf('91', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.54  thf('92', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.54  thf('93', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 0.20/0.54      inference('demod', [status(thm)], ['91', '92'])).
% 0.20/0.54  thf('94', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.20/0.54            = (k10_relat_1 @ X1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['90', '93'])).
% 0.20/0.54  thf('95', plain,
% 0.20/0.54      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup+', [status(thm)], ['85', '94'])).
% 0.20/0.54  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('97', plain,
% 0.20/0.54      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.54  thf('98', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['65', '68', '97'])).
% 0.20/0.54  thf('99', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['64', '98'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
