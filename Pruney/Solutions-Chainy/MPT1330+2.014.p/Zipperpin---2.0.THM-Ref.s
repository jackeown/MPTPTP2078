%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gFomaJtzgW

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 286 expanded)
%              Number of leaves         :   33 (  96 expanded)
%              Depth                    :   20
%              Number of atoms          : 1047 (4619 expanded)
%              Number of equality atoms :   96 ( 364 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X21 @ X19 )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X21 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ k1_xboole_0 @ X19 )
      | ( v1_partfun1 @ X20 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('35',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','40'])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('43',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','47'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('50',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('51',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('58',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    v5_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('72',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('74',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('75',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k10_relat_1 @ X4 @ X5 )
        = ( k10_relat_1 @ X4 @ ( k3_xboole_0 @ ( k2_relat_1 @ X4 ) @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('76',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('78',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','61','78'])).

thf('80',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('82',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['48','82'])).

thf('84',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('85',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','85'])).

thf('87',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','86'])).

thf('88',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('92',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('97',plain,(
    ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['92','95','96'])).

thf('98',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('100',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['90','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gFomaJtzgW
% 0.16/0.35  % Computer   : n022.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % DateTime   : Tue Dec  1 19:50:26 EST 2020
% 0.16/0.35  % CPUTime    : 
% 0.16/0.35  % Running portfolio for 600 s
% 0.16/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 101 iterations in 0.035s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.48  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.48  thf(d3_struct_0, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X22 : $i]:
% 0.22/0.48         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X22 : $i]:
% 0.22/0.48         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.48  thf(t52_tops_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_struct_0 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( l1_struct_0 @ B ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.48                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.48                 ( m1_subset_1 @
% 0.22/0.48                   C @ 
% 0.22/0.48                   ( k1_zfmisc_1 @
% 0.22/0.48                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.48               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.48                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.48                 ( ( k8_relset_1 @
% 0.22/0.48                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.48                     ( k2_struct_0 @ B ) ) =
% 0.22/0.48                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( l1_struct_0 @ A ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( l1_struct_0 @ B ) =>
% 0.22/0.48              ( ![C:$i]:
% 0.22/0.48                ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.48                    ( v1_funct_2 @
% 0.22/0.48                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.48                    ( m1_subset_1 @
% 0.22/0.48                      C @ 
% 0.22/0.48                      ( k1_zfmisc_1 @
% 0.22/0.48                        ( k2_zfmisc_1 @
% 0.22/0.48                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.48                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.48                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.48                    ( ( k8_relset_1 @
% 0.22/0.48                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.48                        ( k2_struct_0 @ B ) ) =
% 0.22/0.48                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ 
% 0.22/0.48        (k1_zfmisc_1 @ 
% 0.22/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t132_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.48       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.48           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.22/0.48           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.48         (((X19) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_funct_1 @ X20)
% 0.22/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.22/0.48          | (v1_partfun1 @ X20 @ X21)
% 0.22/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.22/0.48          | ~ (v1_funct_2 @ X20 @ X21 @ X19)
% 0.22/0.48          | ~ (v1_funct_1 @ X20))),
% 0.22/0.48      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.48         (~ (v1_funct_2 @ X20 @ X21 @ X19)
% 0.22/0.48          | (v1_partfun1 @ X20 @ X21)
% 0.22/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.22/0.48          | ~ (v1_funct_1 @ X20)
% 0.22/0.48          | ((X19) = (k1_xboole_0)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.22/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.48        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.49  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.22/0.49        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.49  thf(d4_partfun1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.49       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i]:
% 0.22/0.49         (~ (v1_partfun1 @ X18 @ X17)
% 0.22/0.49          | ((k1_relat_1 @ X18) = (X17))
% 0.22/0.49          | ~ (v4_relat_1 @ X18 @ X17)
% 0.22/0.49          | ~ (v1_relat_1 @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.22/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.49        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(cc1_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( v1_relat_1 @ C ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         ((v1_relat_1 @ X7)
% 0.22/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.49  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(cc2_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.49         ((v4_relat_1 @ X10 @ X11)
% 0.22/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.49  thf('16', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.22/0.49        | ~ (l1_struct_0 @ sk_B)
% 0.22/0.49        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['1', '17'])).
% 0.22/0.49  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.22/0.49        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.22/0.49         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.22/0.49      inference('split', [status(esa)], ['21'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('split', [status(esa)], ['21'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X22 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (((m1_subset_1 @ sk_C @ 
% 0.22/0.49         (k1_zfmisc_1 @ 
% 0.22/0.49          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.22/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (((m1_subset_1 @ sk_C @ 
% 0.22/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['23', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.49         (((X21) != (k1_xboole_0))
% 0.22/0.49          | ~ (v1_funct_1 @ X20)
% 0.22/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.22/0.49          | (v1_partfun1 @ X20 @ X21)
% 0.22/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.22/0.49          | ~ (v1_funct_2 @ X20 @ X21 @ X19)
% 0.22/0.49          | ~ (v1_funct_1 @ X20))),
% 0.22/0.49      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X19 : $i, X20 : $i]:
% 0.22/0.49         (~ (v1_funct_2 @ X20 @ k1_xboole_0 @ X19)
% 0.22/0.49          | (v1_partfun1 @ X20 @ k1_xboole_0)
% 0.22/0.49          | ~ (m1_subset_1 @ X20 @ 
% 0.22/0.49               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X19)))
% 0.22/0.49          | ~ (v1_funct_1 @ X20))),
% 0.22/0.49      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (((~ (v1_funct_1 @ sk_C)
% 0.22/0.49         | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.22/0.49         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['29', '31'])).
% 0.22/0.49  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('split', [status(esa)], ['21'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (![X22 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.22/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['34', '39'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (((v1_partfun1 @ sk_C @ k1_xboole_0))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('demod', [status(thm)], ['32', '33', '40'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i]:
% 0.22/0.49         (~ (v1_partfun1 @ X18 @ X17)
% 0.22/0.49          | ((k1_relat_1 @ X18) = (X17))
% 0.22/0.49          | ~ (v4_relat_1 @ X18 @ X17)
% 0.22/0.49          | ~ (v1_relat_1 @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (((~ (v1_relat_1 @ sk_C)
% 0.22/0.49         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.22/0.49         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.49  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (((m1_subset_1 @ sk_C @ 
% 0.22/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['23', '28'])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.49         ((v4_relat_1 @ X10 @ X11)
% 0.22/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.22/0.49  thf(t169_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (![X6 : $i]:
% 0.22/0.49         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.22/0.49          | ~ (v1_relat_1 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('split', [status(esa)], ['21'])).
% 0.22/0.49  thf('51', plain,
% 0.22/0.49      (![X22 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('52', plain,
% 0.22/0.49      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.49         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('53', plain,
% 0.22/0.49      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.49          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.22/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.49  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('55', plain,
% 0.22/0.49      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.49         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['53', '54'])).
% 0.22/0.49  thf('56', plain,
% 0.22/0.49      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.49          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['50', '55'])).
% 0.22/0.49  thf('57', plain,
% 0.22/0.49      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('split', [status(esa)], ['21'])).
% 0.22/0.49  thf('58', plain,
% 0.22/0.49      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.49          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.49  thf('59', plain,
% 0.22/0.49      (((m1_subset_1 @ sk_C @ 
% 0.22/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['23', '28'])).
% 0.22/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.49  thf('60', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.22/0.49          | ((k8_relset_1 @ X14 @ X15 @ X13 @ X16) = (k10_relat_1 @ X13 @ X16)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.49  thf('61', plain,
% 0.22/0.49      ((![X0 : $i]:
% 0.22/0.49          ((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ X0)
% 0.22/0.49            = (k10_relat_1 @ sk_C @ X0)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.49  thf('62', plain,
% 0.22/0.49      (![X22 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('63', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('64', plain,
% 0.22/0.49      (((m1_subset_1 @ sk_C @ 
% 0.22/0.49         (k1_zfmisc_1 @ 
% 0.22/0.49          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.22/0.49        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.49      inference('sup+', [status(thm)], ['62', '63'])).
% 0.22/0.49  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('66', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.49  thf('67', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.49         ((v5_relat_1 @ X10 @ X12)
% 0.22/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.49  thf('68', plain, ((v5_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.49  thf(d19_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.49  thf('69', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         (~ (v5_relat_1 @ X2 @ X3)
% 0.22/0.49          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.22/0.49          | ~ (v1_relat_1 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.49  thf('70', plain,
% 0.22/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.49        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.49  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('72', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['70', '71'])).
% 0.22/0.49  thf(t28_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.49  thf('73', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.49  thf('74', plain,
% 0.22/0.49      (((k3_xboole_0 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.22/0.49         = (k2_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['72', '73'])).
% 0.22/0.49  thf(t168_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( k10_relat_1 @ B @ A ) =
% 0.22/0.49         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.22/0.49  thf('75', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i]:
% 0.22/0.49         (((k10_relat_1 @ X4 @ X5)
% 0.22/0.49            = (k10_relat_1 @ X4 @ (k3_xboole_0 @ (k2_relat_1 @ X4) @ X5)))
% 0.22/0.49          | ~ (v1_relat_1 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.22/0.49  thf('76', plain,
% 0.22/0.49      ((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 0.22/0.49          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.22/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup+', [status(thm)], ['74', '75'])).
% 0.22/0.49  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('78', plain,
% 0.22/0.49      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 0.22/0.49         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.22/0.49      inference('demod', [status(thm)], ['76', '77'])).
% 0.22/0.49  thf('79', plain,
% 0.22/0.49      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_xboole_0)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('demod', [status(thm)], ['58', '61', '78'])).
% 0.22/0.49  thf('80', plain,
% 0.22/0.49      (((((k1_relat_1 @ sk_C) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['49', '79'])).
% 0.22/0.49  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('82', plain,
% 0.22/0.49      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.22/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.49      inference('demod', [status(thm)], ['80', '81'])).
% 0.22/0.49  thf('83', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['48', '82'])).
% 0.22/0.49  thf('84', plain,
% 0.22/0.49      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.22/0.49       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('split', [status(esa)], ['21'])).
% 0.22/0.49  thf('85', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.22/0.49  thf('86', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['22', '85'])).
% 0.22/0.49  thf('87', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['20', '86'])).
% 0.22/0.49  thf('88', plain,
% 0.22/0.49      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['0', '87'])).
% 0.22/0.49  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('90', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['88', '89'])).
% 0.22/0.49  thf('91', plain,
% 0.22/0.49      (![X6 : $i]:
% 0.22/0.49         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.22/0.49          | ~ (v1_relat_1 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.22/0.49  thf('92', plain,
% 0.22/0.49      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.49         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('93', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('94', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.22/0.49          | ((k8_relset_1 @ X14 @ X15 @ X13 @ X16) = (k10_relat_1 @ X13 @ X16)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.49  thf('95', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.49           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.49  thf('96', plain,
% 0.22/0.49      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 0.22/0.49         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.22/0.49      inference('demod', [status(thm)], ['76', '77'])).
% 0.22/0.49  thf('97', plain,
% 0.22/0.49      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['92', '95', '96'])).
% 0.22/0.49  thf('98', plain,
% 0.22/0.49      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)) | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['91', '97'])).
% 0.22/0.49  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('100', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['98', '99'])).
% 0.22/0.49  thf('101', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['90', '100'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
