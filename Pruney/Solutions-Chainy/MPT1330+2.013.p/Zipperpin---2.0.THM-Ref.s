%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.erjd4iwsnU

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:43 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 445 expanded)
%              Number of leaves         :   42 ( 143 expanded)
%              Depth                    :   18
%              Number of atoms          : 1053 (6762 expanded)
%              Number of equality atoms :  107 ( 610 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf('0',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ( v1_partfun1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('4',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X33 @ X31 )
      | ( v1_partfun1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_partfun1 @ X29 @ X28 )
      | ( ( k1_relat_1 @ X29 )
        = X28 )
      | ~ ( v4_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','13','16'])).

thf('18',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('24',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('31',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('33',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','40'])).

thf(t171_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf('42',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k8_relset_1 @ X35 @ X35 @ ( k6_partfun1 @ X35 ) @ X34 )
        = X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf('43',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_C )
      = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('44',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('45',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('46',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('47',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('48',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k8_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k10_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t172_relat_1,axiom,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('50',plain,(
    ! [X9: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','46','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','52','53'])).

thf('55',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('57',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','58'])).

thf('60',plain,(
    ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','59'])).

thf('61',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','58'])).

thf('63',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','58'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k8_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k10_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('78',plain,(
    v5_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('79',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('82',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('83',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('84',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('85',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ X14 @ ( k6_partfun1 @ X15 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('88',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('89',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('90',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('91',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('92',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('94',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('95',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('96',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['93','96'])).

thf('98',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['88','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('100',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','71','100'])).

thf('102',plain,(
    $false ),
    inference(simplify,[status(thm)],['101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.erjd4iwsnU
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:43:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 368 iterations in 0.193s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.66  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.66  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.66  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.47/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.66  thf(t52_tops_2, conjecture,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_struct_0 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( l1_struct_0 @ B ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.66                 ( m1_subset_1 @
% 0.47/0.66                   C @ 
% 0.47/0.66                   ( k1_zfmisc_1 @
% 0.47/0.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.66               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.66                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.66                 ( ( k8_relset_1 @
% 0.47/0.66                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.47/0.66                     ( k2_struct_0 @ B ) ) =
% 0.47/0.66                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i]:
% 0.47/0.66        ( ( l1_struct_0 @ A ) =>
% 0.47/0.66          ( ![B:$i]:
% 0.47/0.66            ( ( l1_struct_0 @ B ) =>
% 0.47/0.66              ( ![C:$i]:
% 0.47/0.66                ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.66                    ( v1_funct_2 @
% 0.47/0.66                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.66                    ( m1_subset_1 @
% 0.47/0.66                      C @ 
% 0.47/0.66                      ( k1_zfmisc_1 @
% 0.47/0.66                        ( k2_zfmisc_1 @
% 0.47/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.66                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.66                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.66                    ( ( k8_relset_1 @
% 0.47/0.66                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.47/0.66                        ( k2_struct_0 @ B ) ) =
% 0.47/0.66                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.66         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d3_struct_0, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (![X36 : $i]:
% 0.47/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ 
% 0.47/0.66        (k1_zfmisc_1 @ 
% 0.47/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t132_funct_2, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.66       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.66           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.66           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.66         (((X31) = (k1_xboole_0))
% 0.47/0.66          | ~ (v1_funct_1 @ X32)
% 0.47/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 0.47/0.66          | (v1_partfun1 @ X32 @ X33)
% 0.47/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 0.47/0.66          | ~ (v1_funct_2 @ X32 @ X33 @ X31)
% 0.47/0.66          | ~ (v1_funct_1 @ X32))),
% 0.47/0.66      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.66         (~ (v1_funct_2 @ X32 @ X33 @ X31)
% 0.47/0.66          | (v1_partfun1 @ X32 @ X33)
% 0.47/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 0.47/0.66          | ~ (v1_funct_1 @ X32)
% 0.47/0.66          | ((X31) = (k1_xboole_0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['3'])).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.47/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['2', '4'])).
% 0.47/0.66  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.47/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.47/0.66  thf(d4_partfun1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.66       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (![X28 : $i, X29 : $i]:
% 0.47/0.66         (~ (v1_partfun1 @ X29 @ X28)
% 0.47/0.66          | ((k1_relat_1 @ X29) = (X28))
% 0.47/0.66          | ~ (v4_relat_1 @ X29 @ X28)
% 0.47/0.66          | ~ (v1_relat_1 @ X29))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.47/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.66        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ 
% 0.47/0.66        (k1_zfmisc_1 @ 
% 0.47/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc1_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( v1_relat_1 @ C ) ))).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.66         ((v1_relat_1 @ X18)
% 0.47/0.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.66  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ 
% 0.47/0.66        (k1_zfmisc_1 @ 
% 0.47/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc2_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.66         ((v4_relat_1 @ X21 @ X22)
% 0.47/0.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.66  thf('16', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.47/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.47/0.66        | ~ (l1_struct_0 @ sk_B)
% 0.47/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['1', '17'])).
% 0.47/0.66  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.47/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.47/0.66        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.47/0.66         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['21'])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.47/0.66         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['21'])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (![X36 : $i]:
% 0.47/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.66         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.66          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.47/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.66  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.66         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.66          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.47/0.66         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['23', '28'])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.47/0.66         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['21'])).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.66          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.47/0.66         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.47/0.66         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['21'])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X36 : $i]:
% 0.47/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ 
% 0.47/0.66        (k1_zfmisc_1 @ 
% 0.47/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (((m1_subset_1 @ sk_C @ 
% 0.47/0.66         (k1_zfmisc_1 @ 
% 0.47/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.47/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup+', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ 
% 0.47/0.66        (k1_zfmisc_1 @ 
% 0.47/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.66      inference('demod', [status(thm)], ['35', '36'])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (((m1_subset_1 @ sk_C @ 
% 0.47/0.66         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.47/0.66         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['32', '37'])).
% 0.47/0.66  thf(t113_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X1 : $i, X2 : $i]:
% 0.47/0.66         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.66         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['38', '40'])).
% 0.47/0.66  thf(t171_funct_2, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.66       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (![X34 : $i, X35 : $i]:
% 0.47/0.66         (((k8_relset_1 @ X35 @ X35 @ (k6_partfun1 @ X35) @ X34) = (X34))
% 0.47/0.66          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t171_funct_2])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      ((((k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.47/0.66          (k6_partfun1 @ k1_xboole_0) @ sk_C) = (sk_C)))
% 0.47/0.66         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.66  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.47/0.66  thf('44', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.66  thf(redefinition_k6_partfun1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.47/0.66  thf('45', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('46', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['44', '45'])).
% 0.47/0.66  thf(t4_subset_1, axiom,
% 0.47/0.66    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.66  thf(redefinition_k8_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.47/0.66          | ((k8_relset_1 @ X25 @ X26 @ X24 @ X27) = (k10_relat_1 @ X24 @ X27)))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.47/0.66           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.47/0.66      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.66  thf(t172_relat_1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.47/0.66  thf('50', plain,
% 0.47/0.66      (![X9 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t172_relat_1])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['49', '50'])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      ((((k1_xboole_0) = (sk_C))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['43', '46', '51'])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['49', '50'])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.47/0.66         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['31', '52', '53'])).
% 0.47/0.66  thf('55', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['54'])).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.47/0.66       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('split', [status(esa)], ['21'])).
% 0.47/0.66  thf('57', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.47/0.66  thf('58', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['22', '57'])).
% 0.47/0.66  thf('59', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['20', '58'])).
% 0.47/0.66  thf('60', plain,
% 0.47/0.66      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.66         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['0', '59'])).
% 0.47/0.66  thf('61', plain,
% 0.47/0.66      (![X36 : $i]:
% 0.47/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.66  thf('62', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['20', '58'])).
% 0.47/0.66  thf('63', plain,
% 0.47/0.66      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup+', [status(thm)], ['61', '62'])).
% 0.47/0.66  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('65', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['63', '64'])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.66         (k2_struct_0 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.47/0.66      inference('demod', [status(thm)], ['60', '65'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ 
% 0.47/0.66        (k1_zfmisc_1 @ 
% 0.47/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('68', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['20', '58'])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ 
% 0.47/0.66        (k1_zfmisc_1 @ 
% 0.47/0.66         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.66  thf('70', plain,
% 0.47/0.66      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.47/0.66          | ((k8_relset_1 @ X25 @ X26 @ X24 @ X27) = (k10_relat_1 @ X24 @ X27)))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.47/0.66  thf('71', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ X0)
% 0.47/0.66           = (k10_relat_1 @ sk_C @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['69', '70'])).
% 0.47/0.66  thf('72', plain,
% 0.47/0.66      (![X36 : $i]:
% 0.47/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.66  thf('73', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ 
% 0.47/0.66        (k1_zfmisc_1 @ 
% 0.47/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('74', plain,
% 0.47/0.66      (((m1_subset_1 @ sk_C @ 
% 0.47/0.66         (k1_zfmisc_1 @ 
% 0.47/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.66      inference('sup+', [status(thm)], ['72', '73'])).
% 0.47/0.66  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('76', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ 
% 0.47/0.66        (k1_zfmisc_1 @ 
% 0.47/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.66      inference('demod', [status(thm)], ['74', '75'])).
% 0.47/0.66  thf('77', plain,
% 0.47/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.66         ((v5_relat_1 @ X21 @ X23)
% 0.47/0.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.66  thf('78', plain, ((v5_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['76', '77'])).
% 0.47/0.66  thf(d19_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ B ) =>
% 0.47/0.66       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.66  thf('79', plain,
% 0.47/0.66      (![X7 : $i, X8 : $i]:
% 0.47/0.66         (~ (v5_relat_1 @ X7 @ X8)
% 0.47/0.66          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.47/0.66          | ~ (v1_relat_1 @ X7))),
% 0.47/0.66      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.47/0.66  thf('80', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.66        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['78', '79'])).
% 0.47/0.66  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.66  thf('82', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['80', '81'])).
% 0.47/0.66  thf(t79_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ B ) =>
% 0.47/0.66       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.47/0.66         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.47/0.66  thf('83', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.47/0.66          | ((k5_relat_1 @ X14 @ (k6_relat_1 @ X15)) = (X14))
% 0.47/0.66          | ~ (v1_relat_1 @ X14))),
% 0.47/0.66      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.47/0.66  thf('84', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('85', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.47/0.66          | ((k5_relat_1 @ X14 @ (k6_partfun1 @ X15)) = (X14))
% 0.47/0.66          | ~ (v1_relat_1 @ X14))),
% 0.47/0.66      inference('demod', [status(thm)], ['83', '84'])).
% 0.47/0.66  thf('86', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.66        | ((k5_relat_1 @ sk_C @ (k6_partfun1 @ (k2_struct_0 @ sk_B))) = (sk_C)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['82', '85'])).
% 0.47/0.66  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.66  thf('88', plain,
% 0.47/0.66      (((k5_relat_1 @ sk_C @ (k6_partfun1 @ (k2_struct_0 @ sk_B))) = (sk_C))),
% 0.47/0.66      inference('demod', [status(thm)], ['86', '87'])).
% 0.47/0.66  thf(t71_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.47/0.66       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.47/0.66  thf('89', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.47/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.66  thf('90', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('91', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 0.47/0.66      inference('demod', [status(thm)], ['89', '90'])).
% 0.47/0.66  thf(t182_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( v1_relat_1 @ B ) =>
% 0.47/0.66           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.47/0.66             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.47/0.66  thf('92', plain,
% 0.47/0.66      (![X10 : $i, X11 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X10)
% 0.47/0.66          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 0.47/0.66              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 0.47/0.66          | ~ (v1_relat_1 @ X11))),
% 0.47/0.66      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.47/0.66  thf('93', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.47/0.66            = (k10_relat_1 @ X1 @ X0))
% 0.47/0.66          | ~ (v1_relat_1 @ X1)
% 0.47/0.66          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['91', '92'])).
% 0.47/0.66  thf(fc3_funct_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.66       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.66  thf('94', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('95', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('96', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.47/0.66      inference('demod', [status(thm)], ['94', '95'])).
% 0.47/0.66  thf('97', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.47/0.66            = (k10_relat_1 @ X1 @ X0))
% 0.47/0.66          | ~ (v1_relat_1 @ X1))),
% 0.47/0.66      inference('demod', [status(thm)], ['93', '96'])).
% 0.47/0.66  thf('98', plain,
% 0.47/0.66      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))
% 0.47/0.66        | ~ (v1_relat_1 @ sk_C))),
% 0.47/0.66      inference('sup+', [status(thm)], ['88', '97'])).
% 0.47/0.66  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.66  thf('100', plain,
% 0.47/0.66      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['98', '99'])).
% 0.47/0.66  thf('101', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.47/0.66      inference('demod', [status(thm)], ['66', '71', '100'])).
% 0.47/0.66  thf('102', plain, ($false), inference('simplify', [status(thm)], ['101'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
