%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WG9Jvr8L9q

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:42 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 823 expanded)
%              Number of leaves         :   35 ( 246 expanded)
%              Depth                    :   23
%              Number of atoms          : 1205 (13510 expanded)
%              Number of equality atoms :  111 (1110 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
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

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_partfun1 @ X29 @ X28 )
      | ( ( k1_relat_1 @ X29 )
        = X28 )
      | ~ ( v4_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','21','28'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('39',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('47',plain,
    ( ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('52',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k8_relset_1 @ X22 @ X23 @ X24 @ X23 )
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('53',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('55',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('56',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('58',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('63',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('65',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('66',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','67'])).

thf('69',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','68'])).

thf('70',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('72',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('79',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['69','82'])).

thf('84',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('85',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','85'])).

thf('87',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['34','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','87'])).

thf('89',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k8_relset_1 @ X22 @ X23 @ X24 @ X23 )
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('90',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('94',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['34','86'])).

thf('99',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','99'])).

thf('101',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['34','86'])).

thf('106',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('109',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_partfun1 @ X29 @ X28 )
      | ( ( k1_relat_1 @ X29 )
        = X28 )
      | ~ ( v4_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('112',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('115',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['107','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','85'])).

thf('120',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

thf('121',plain,(
    ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','120'])).

thf('122',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['103','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WG9Jvr8L9q
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:24:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.62/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.62/0.84  % Solved by: fo/fo7.sh
% 0.62/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.84  % done 693 iterations in 0.382s
% 0.62/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.62/0.84  % SZS output start Refutation
% 0.62/0.84  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.62/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.62/0.84  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.62/0.84  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.62/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.62/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.84  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.62/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.62/0.84  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.62/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.62/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.62/0.84  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.62/0.84  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.62/0.84  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.62/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.62/0.84  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.62/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.62/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.84  thf(d3_struct_0, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.62/0.84  thf('0', plain,
% 0.62/0.84      (![X30 : $i]:
% 0.62/0.84         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.62/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.84  thf('1', plain,
% 0.62/0.84      (![X30 : $i]:
% 0.62/0.84         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.62/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.84  thf(t52_tops_2, conjecture,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( l1_struct_0 @ A ) =>
% 0.62/0.84       ( ![B:$i]:
% 0.62/0.84         ( ( l1_struct_0 @ B ) =>
% 0.62/0.84           ( ![C:$i]:
% 0.62/0.84             ( ( ( v1_funct_1 @ C ) & 
% 0.62/0.84                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.62/0.84                 ( m1_subset_1 @
% 0.62/0.84                   C @ 
% 0.62/0.84                   ( k1_zfmisc_1 @
% 0.62/0.84                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.62/0.84               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.62/0.84                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.62/0.84                 ( ( k8_relset_1 @
% 0.62/0.84                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.62/0.84                     ( k2_struct_0 @ B ) ) =
% 0.62/0.84                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.62/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.84    (~( ![A:$i]:
% 0.62/0.84        ( ( l1_struct_0 @ A ) =>
% 0.62/0.84          ( ![B:$i]:
% 0.62/0.84            ( ( l1_struct_0 @ B ) =>
% 0.62/0.84              ( ![C:$i]:
% 0.62/0.84                ( ( ( v1_funct_1 @ C ) & 
% 0.62/0.84                    ( v1_funct_2 @
% 0.62/0.84                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.62/0.84                    ( m1_subset_1 @
% 0.62/0.84                      C @ 
% 0.62/0.84                      ( k1_zfmisc_1 @
% 0.62/0.84                        ( k2_zfmisc_1 @
% 0.62/0.84                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.62/0.84                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.62/0.84                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.62/0.84                    ( ( k8_relset_1 @
% 0.62/0.84                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.62/0.84                        ( k2_struct_0 @ B ) ) =
% 0.62/0.84                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.62/0.84    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.62/0.84  thf('2', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ 
% 0.62/0.84        (k1_zfmisc_1 @ 
% 0.62/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('3', plain,
% 0.62/0.84      (((m1_subset_1 @ sk_C @ 
% 0.62/0.84         (k1_zfmisc_1 @ 
% 0.62/0.84          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.62/0.84        | ~ (l1_struct_0 @ sk_A))),
% 0.62/0.84      inference('sup+', [status(thm)], ['1', '2'])).
% 0.62/0.84  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('5', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ 
% 0.62/0.84        (k1_zfmisc_1 @ 
% 0.62/0.84         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.84      inference('demod', [status(thm)], ['3', '4'])).
% 0.62/0.84  thf('6', plain,
% 0.62/0.84      (![X30 : $i]:
% 0.62/0.84         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.62/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.84  thf('7', plain,
% 0.62/0.84      (![X30 : $i]:
% 0.62/0.84         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.62/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.84  thf('8', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ 
% 0.62/0.84        (k1_zfmisc_1 @ 
% 0.62/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(cc5_funct_2, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.62/0.84       ( ![C:$i]:
% 0.62/0.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.84           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.62/0.84             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.62/0.84  thf('9', plain,
% 0.62/0.84      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.62/0.84          | (v1_partfun1 @ X25 @ X26)
% 0.62/0.84          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.62/0.84          | ~ (v1_funct_1 @ X25)
% 0.62/0.84          | (v1_xboole_0 @ X27))),
% 0.62/0.84      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.62/0.84  thf('10', plain,
% 0.62/0.84      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.62/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.62/0.84        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.62/0.84        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['8', '9'])).
% 0.62/0.84  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('12', plain,
% 0.62/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('13', plain,
% 0.62/0.84      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.62/0.84        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.62/0.84      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.62/0.84  thf('14', plain,
% 0.62/0.84      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.62/0.84        | ~ (l1_struct_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.62/0.84      inference('sup+', [status(thm)], ['7', '13'])).
% 0.62/0.84  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('16', plain,
% 0.62/0.84      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.62/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.62/0.84      inference('demod', [status(thm)], ['14', '15'])).
% 0.62/0.84  thf(d4_partfun1, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.62/0.84       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.62/0.84  thf('17', plain,
% 0.62/0.84      (![X28 : $i, X29 : $i]:
% 0.62/0.84         (~ (v1_partfun1 @ X29 @ X28)
% 0.62/0.84          | ((k1_relat_1 @ X29) = (X28))
% 0.62/0.84          | ~ (v4_relat_1 @ X29 @ X28)
% 0.62/0.84          | ~ (v1_relat_1 @ X29))),
% 0.62/0.84      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.62/0.84  thf('18', plain,
% 0.62/0.84      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.62/0.84        | ~ (v1_relat_1 @ sk_C)
% 0.62/0.84        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.62/0.84        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['16', '17'])).
% 0.62/0.84  thf('19', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ 
% 0.62/0.84        (k1_zfmisc_1 @ 
% 0.62/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(cc1_relset_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.84       ( v1_relat_1 @ C ) ))).
% 0.62/0.84  thf('20', plain,
% 0.62/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.62/0.84         ((v1_relat_1 @ X12)
% 0.62/0.84          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.62/0.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.62/0.84  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.84      inference('sup-', [status(thm)], ['19', '20'])).
% 0.62/0.84  thf('22', plain,
% 0.62/0.84      (![X30 : $i]:
% 0.62/0.84         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.62/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.84  thf('23', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ 
% 0.62/0.84        (k1_zfmisc_1 @ 
% 0.62/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(cc2_relset_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.84       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.62/0.84  thf('24', plain,
% 0.62/0.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.62/0.84         ((v4_relat_1 @ X15 @ X16)
% 0.62/0.84          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.62/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.62/0.84  thf('25', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['23', '24'])).
% 0.62/0.84  thf('26', plain,
% 0.62/0.84      (((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.62/0.84      inference('sup+', [status(thm)], ['22', '25'])).
% 0.62/0.84  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('28', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.62/0.84      inference('demod', [status(thm)], ['26', '27'])).
% 0.62/0.84  thf('29', plain,
% 0.62/0.84      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.62/0.84        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.62/0.84      inference('demod', [status(thm)], ['18', '21', '28'])).
% 0.62/0.84  thf(l13_xboole_0, axiom,
% 0.62/0.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.62/0.84  thf('30', plain,
% 0.62/0.84      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.62/0.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.62/0.84  thf('31', plain,
% 0.62/0.84      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.62/0.84        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.62/0.84  thf('32', plain,
% 0.62/0.84      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.62/0.84        | ~ (l1_struct_0 @ sk_B)
% 0.62/0.84        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.62/0.84      inference('sup+', [status(thm)], ['6', '31'])).
% 0.62/0.84  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('34', plain,
% 0.62/0.84      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.62/0.84        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.62/0.84      inference('demod', [status(thm)], ['32', '33'])).
% 0.62/0.84  thf('35', plain,
% 0.62/0.84      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.62/0.84        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('36', plain,
% 0.62/0.84      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.62/0.84         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.62/0.84      inference('split', [status(esa)], ['35'])).
% 0.62/0.84  thf('37', plain,
% 0.62/0.84      (![X30 : $i]:
% 0.62/0.84         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.62/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.84  thf('38', plain,
% 0.62/0.84      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('split', [status(esa)], ['35'])).
% 0.62/0.84  thf('39', plain,
% 0.62/0.84      (![X30 : $i]:
% 0.62/0.84         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.62/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.84  thf('40', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ 
% 0.62/0.84        (k1_zfmisc_1 @ 
% 0.62/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(t3_subset, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.62/0.84  thf('41', plain,
% 0.62/0.84      (![X4 : $i, X5 : $i]:
% 0.62/0.84         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.62/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.62/0.84  thf('42', plain,
% 0.62/0.84      ((r1_tarski @ sk_C @ 
% 0.62/0.84        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.62/0.84  thf('43', plain,
% 0.62/0.84      (((r1_tarski @ sk_C @ 
% 0.62/0.84         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.62/0.84        | ~ (l1_struct_0 @ sk_A))),
% 0.62/0.84      inference('sup+', [status(thm)], ['39', '42'])).
% 0.62/0.84  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('45', plain,
% 0.62/0.84      ((r1_tarski @ sk_C @ 
% 0.62/0.84        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.62/0.84      inference('demod', [status(thm)], ['43', '44'])).
% 0.62/0.84  thf('46', plain,
% 0.62/0.84      (((r1_tarski @ sk_C @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup+', [status(thm)], ['38', '45'])).
% 0.62/0.84  thf('47', plain,
% 0.62/0.84      ((((r1_tarski @ sk_C @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))
% 0.62/0.84         | ~ (l1_struct_0 @ sk_B)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup+', [status(thm)], ['37', '46'])).
% 0.62/0.84  thf('48', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('49', plain,
% 0.62/0.84      (((r1_tarski @ sk_C @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('demod', [status(thm)], ['47', '48'])).
% 0.62/0.84  thf('50', plain,
% 0.62/0.84      (![X4 : $i, X6 : $i]:
% 0.62/0.84         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.62/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.62/0.84  thf('51', plain,
% 0.62/0.84      (((m1_subset_1 @ sk_C @ 
% 0.62/0.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['49', '50'])).
% 0.62/0.84  thf(t38_relset_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.84       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.62/0.84         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.62/0.84  thf('52', plain,
% 0.62/0.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.62/0.84         (((k8_relset_1 @ X22 @ X23 @ X24 @ X23)
% 0.62/0.84            = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.62/0.84          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.62/0.84      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.62/0.84  thf('53', plain,
% 0.62/0.84      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84          (k2_struct_0 @ sk_B))
% 0.62/0.84          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['51', '52'])).
% 0.62/0.84  thf('54', plain,
% 0.62/0.84      (((m1_subset_1 @ sk_C @ 
% 0.62/0.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['49', '50'])).
% 0.62/0.84  thf(redefinition_k1_relset_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.62/0.84  thf('55', plain,
% 0.62/0.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.62/0.84         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.62/0.84          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.62/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.62/0.84  thf('56', plain,
% 0.62/0.84      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.62/0.84          = (k1_relat_1 @ sk_C)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['54', '55'])).
% 0.62/0.84  thf('57', plain,
% 0.62/0.84      (((r1_tarski @ sk_C @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup+', [status(thm)], ['38', '45'])).
% 0.62/0.84  thf('58', plain,
% 0.62/0.84      (![X4 : $i, X6 : $i]:
% 0.62/0.84         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.62/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.62/0.84  thf('59', plain,
% 0.62/0.84      (((m1_subset_1 @ sk_C @ 
% 0.62/0.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['57', '58'])).
% 0.62/0.84  thf('60', plain,
% 0.62/0.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.62/0.84         ((v4_relat_1 @ X15 @ X16)
% 0.62/0.84          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.62/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.62/0.84  thf('61', plain,
% 0.62/0.84      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['59', '60'])).
% 0.62/0.84  thf(d18_relat_1, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( v1_relat_1 @ B ) =>
% 0.62/0.84       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.62/0.84  thf('62', plain,
% 0.62/0.84      (![X7 : $i, X8 : $i]:
% 0.62/0.84         (~ (v4_relat_1 @ X7 @ X8)
% 0.62/0.84          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.62/0.84          | ~ (v1_relat_1 @ X7))),
% 0.62/0.84      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.62/0.84  thf('63', plain,
% 0.62/0.84      (((~ (v1_relat_1 @ sk_C)
% 0.62/0.84         | (r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['61', '62'])).
% 0.62/0.84  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.84      inference('sup-', [status(thm)], ['19', '20'])).
% 0.62/0.84  thf('65', plain,
% 0.62/0.84      (((r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('demod', [status(thm)], ['63', '64'])).
% 0.62/0.84  thf(t3_xboole_1, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.62/0.84  thf('66', plain,
% 0.62/0.84      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.62/0.84      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.62/0.84  thf('67', plain,
% 0.62/0.84      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['65', '66'])).
% 0.62/0.84  thf('68', plain,
% 0.62/0.84      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.62/0.84          = (k1_xboole_0)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('demod', [status(thm)], ['56', '67'])).
% 0.62/0.84  thf('69', plain,
% 0.62/0.84      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84          (k2_struct_0 @ sk_B)) = (k1_xboole_0)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('demod', [status(thm)], ['53', '68'])).
% 0.62/0.84  thf('70', plain,
% 0.62/0.84      (![X30 : $i]:
% 0.62/0.84         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.62/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.84  thf('71', plain,
% 0.62/0.84      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('split', [status(esa)], ['35'])).
% 0.62/0.84  thf('72', plain,
% 0.62/0.84      (![X30 : $i]:
% 0.62/0.84         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.62/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.84  thf('73', plain,
% 0.62/0.84      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('74', plain,
% 0.62/0.84      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.62/0.84        | ~ (l1_struct_0 @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['72', '73'])).
% 0.62/0.84  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('76', plain,
% 0.62/0.84      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.62/0.84      inference('demod', [status(thm)], ['74', '75'])).
% 0.62/0.84  thf('77', plain,
% 0.62/0.84      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['71', '76'])).
% 0.62/0.84  thf('78', plain,
% 0.62/0.84      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('split', [status(esa)], ['35'])).
% 0.62/0.84  thf('79', plain,
% 0.62/0.84      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('demod', [status(thm)], ['77', '78'])).
% 0.62/0.84  thf('80', plain,
% 0.62/0.84      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84           (k2_struct_0 @ sk_B)) != (k1_xboole_0))
% 0.62/0.84         | ~ (l1_struct_0 @ sk_B)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['70', '79'])).
% 0.62/0.84  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('82', plain,
% 0.62/0.84      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.62/0.84         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.84      inference('demod', [status(thm)], ['80', '81'])).
% 0.62/0.84  thf('83', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.62/0.84      inference('simplify_reflect-', [status(thm)], ['69', '82'])).
% 0.62/0.84  thf('84', plain,
% 0.62/0.84      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.62/0.84       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.62/0.84      inference('split', [status(esa)], ['35'])).
% 0.62/0.84  thf('85', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.62/0.84      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.62/0.84  thf('86', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.62/0.84      inference('simpl_trail', [status(thm)], ['36', '85'])).
% 0.62/0.84  thf('87', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.62/0.84      inference('simplify_reflect-', [status(thm)], ['34', '86'])).
% 0.62/0.84  thf('88', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ 
% 0.62/0.84        (k1_zfmisc_1 @ 
% 0.62/0.84         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.84      inference('demod', [status(thm)], ['5', '87'])).
% 0.62/0.84  thf('89', plain,
% 0.62/0.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.62/0.84         (((k8_relset_1 @ X22 @ X23 @ X24 @ X23)
% 0.62/0.84            = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.62/0.84          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.62/0.84      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.62/0.84  thf('90', plain,
% 0.62/0.84      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84         (u1_struct_0 @ sk_B))
% 0.62/0.84         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.62/0.84      inference('sup-', [status(thm)], ['88', '89'])).
% 0.62/0.84  thf('91', plain,
% 0.62/0.84      (![X30 : $i]:
% 0.62/0.84         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.62/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.84  thf('92', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ 
% 0.62/0.84        (k1_zfmisc_1 @ 
% 0.62/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('93', plain,
% 0.62/0.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.62/0.84         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.62/0.84          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.62/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.62/0.84  thf('94', plain,
% 0.62/0.84      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.62/0.84         = (k1_relat_1 @ sk_C))),
% 0.62/0.84      inference('sup-', [status(thm)], ['92', '93'])).
% 0.62/0.84  thf('95', plain,
% 0.62/0.84      ((((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.62/0.84          = (k1_relat_1 @ sk_C))
% 0.62/0.84        | ~ (l1_struct_0 @ sk_A))),
% 0.62/0.84      inference('sup+', [status(thm)], ['91', '94'])).
% 0.62/0.84  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('97', plain,
% 0.62/0.84      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.62/0.84         = (k1_relat_1 @ sk_C))),
% 0.62/0.84      inference('demod', [status(thm)], ['95', '96'])).
% 0.62/0.84  thf('98', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.62/0.84      inference('simplify_reflect-', [status(thm)], ['34', '86'])).
% 0.62/0.84  thf('99', plain,
% 0.62/0.84      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.62/0.84         = (k1_relat_1 @ sk_C))),
% 0.62/0.84      inference('demod', [status(thm)], ['97', '98'])).
% 0.62/0.84  thf('100', plain,
% 0.62/0.84      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84         (u1_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.62/0.84      inference('demod', [status(thm)], ['90', '99'])).
% 0.62/0.84  thf('101', plain,
% 0.62/0.84      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.84          (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))
% 0.62/0.84        | ~ (l1_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['0', '100'])).
% 0.62/0.85  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('103', plain,
% 0.62/0.85      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.85         (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['101', '102'])).
% 0.62/0.85  thf('104', plain,
% 0.62/0.85      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.85         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('105', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.62/0.85      inference('simplify_reflect-', [status(thm)], ['34', '86'])).
% 0.62/0.85  thf('106', plain,
% 0.62/0.85      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.85         (k2_struct_0 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['104', '105'])).
% 0.62/0.85  thf('107', plain,
% 0.62/0.85      (![X30 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('108', plain,
% 0.62/0.85      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.62/0.85        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.62/0.85  thf('109', plain,
% 0.62/0.85      (![X28 : $i, X29 : $i]:
% 0.62/0.85         (~ (v1_partfun1 @ X29 @ X28)
% 0.62/0.85          | ((k1_relat_1 @ X29) = (X28))
% 0.62/0.85          | ~ (v4_relat_1 @ X29 @ X28)
% 0.62/0.85          | ~ (v1_relat_1 @ X29))),
% 0.62/0.85      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.62/0.85  thf('110', plain,
% 0.62/0.85      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.62/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.62/0.85        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.62/0.85        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['108', '109'])).
% 0.62/0.85  thf('111', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['19', '20'])).
% 0.62/0.85  thf('112', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('sup-', [status(thm)], ['23', '24'])).
% 0.62/0.85  thf('113', plain,
% 0.62/0.85      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.62/0.85        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.62/0.85  thf('114', plain,
% 0.62/0.85      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.62/0.85      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.62/0.85  thf('115', plain,
% 0.62/0.85      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.62/0.85        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['113', '114'])).
% 0.62/0.85  thf('116', plain,
% 0.62/0.85      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.62/0.85        | ~ (l1_struct_0 @ sk_B)
% 0.62/0.85        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['107', '115'])).
% 0.62/0.85  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('118', plain,
% 0.62/0.85      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.62/0.85        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('demod', [status(thm)], ['116', '117'])).
% 0.62/0.85  thf('119', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.62/0.85      inference('simpl_trail', [status(thm)], ['36', '85'])).
% 0.62/0.85  thf('120', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 0.62/0.85  thf('121', plain,
% 0.62/0.85      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.62/0.85         (k2_struct_0 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['106', '120'])).
% 0.62/0.85  thf('122', plain, ($false),
% 0.62/0.85      inference('simplify_reflect-', [status(thm)], ['103', '121'])).
% 0.62/0.85  
% 0.62/0.85  % SZS output end Refutation
% 0.62/0.85  
% 0.62/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
