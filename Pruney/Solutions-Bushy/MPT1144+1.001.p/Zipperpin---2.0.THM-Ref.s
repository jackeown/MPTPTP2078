%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1144+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kceAqhBSFu

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:08 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  427 (2437 expanded)
%              Number of leaves         :   38 ( 685 expanded)
%              Depth                    :   48
%              Number of atoms          : 5370 (48571 expanded)
%              Number of equality atoms :  166 ( 710 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r7_relat_2_type,type,(
    r7_relat_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_domain_1_type,type,(
    k7_domain_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(t36_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A )
                  & ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
              <=> ( ( r3_orders_2 @ A @ B @ C )
                  | ( r3_orders_2 @ A @ C @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A )
                    & ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                <=> ( ( r3_orders_2 @ A @ B @ C )
                    | ( r3_orders_2 @ A @ C @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_orders_2])).

thf('0',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( ( k7_domain_1 @ A @ B @ C )
        = ( k2_tarski @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( ( k7_domain_1 @ X28 @ X27 @ X29 )
        = ( k2_tarski @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_domain_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_tarski @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B )
      = ( k2_tarski @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( m1_subset_1 @ ( k7_domain_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( m1_subset_1 @ ( k7_domain_1 @ X22 @ X21 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(d11_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_orders_2 @ B @ A )
          <=> ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r7_relat_2 @ ( u1_orders_2 @ X6 ) @ X5 )
      | ( v6_orders_2 @ X5 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B ) @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B ) @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,
    ( ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_B ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X25: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( u1_orders_2 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('30',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r3_orders_2 @ X33 @ X34 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_orders_2 @ X33 )
      | ~ ( v3_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    r3_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( r1_orders_2 @ X31 @ X30 @ X32 )
      | ~ ( r3_orders_2 @ X31 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['27','48'])).

thf(d7_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r7_relat_2 @ A @ B )
        <=> ! [C: $i,D: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ D @ B )
                & ~ ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
                & ~ ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) )).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X13 @ X14 ) @ X13 )
      | ( r7_relat_2 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ( X11 = X10 )
      | ( X11 = X7 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('52',plain,(
    ! [X7: $i,X10: $i,X11: $i] :
      ( ( X11 = X7 )
      | ( X11 = X10 )
      | ~ ( r2_hidden @ X11 @ ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['53'])).

thf('55',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X2 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X2 @ X2 ) @ X1 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_C @ X13 @ X14 ) @ X13 )
      | ( r7_relat_2 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('57',plain,(
    ! [X7: $i,X10: $i,X11: $i] :
      ( ( X11 = X7 )
      | ( X11 = X10 )
      | ~ ( r2_hidden @ X11 @ ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['58'])).

thf('60',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X2 ) )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X2 ) @ X1 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X14 ) @ ( sk_D_1 @ X13 @ X14 ) ) @ X14 )
      | ( r7_relat_2 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_B ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','65'])).

thf('67',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','66'])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('74',plain,
    ( ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( r1_orders_2 @ X31 @ X30 @ X32 )
      | ~ ( r3_orders_2 @ X31 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( u1_orders_2 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('96',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('98',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X14 ) @ ( sk_D_1 @ X13 @ X14 ) ) @ X14 )
      | ( r7_relat_2 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) ) @ X1 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X1 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['96','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ X1 )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X0 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_B ) )
      | ( ( sk_C @ ( k2_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','103'])).

thf('105',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('106',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('107',plain,
    ( ( ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','108'])).

thf('110',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X1 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['96','100'])).

thf('113',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_B ) )
      | ( ( sk_C @ ( k2_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('116',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r3_orders_2 @ X33 @ X34 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_orders_2 @ X33 )
      | ~ ( v3_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    r3_orders_2 @ sk_A @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['117','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    r1_orders_2 @ sk_A @ sk_C_1 @ sk_C_1 ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['116','132'])).

thf('134',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('135',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('136',plain,
    ( ( ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['113','133','134','135'])).

thf('137',plain,
    ( ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','137'])).

thf('139',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('143',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X14 ) @ ( sk_C @ X13 @ X14 ) ) @ X14 )
      | ( r7_relat_2 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ X1 ) ) @ X1 )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X1 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['141','145'])).

thf('147',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_B ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['140','146'])).

thf('148',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('149',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('150',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('151',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['147','148','149','150'])).

thf('152',plain,
    ( ( ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['71','152'])).

thf('154',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('157',plain,
    ( ( ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('158',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('160',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X14 ) @ ( sk_D_1 @ X13 @ X14 ) ) @ X14 )
      | ( r7_relat_2 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_tarski @ X2 @ X0 ) @ X1 ) @ X0 ) @ X1 )
      | ( ( sk_D_1 @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X2 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_tarski @ X2 @ X0 ) @ X1 ) @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 ) @ X1 ) @ X2 )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X0 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['158','162'])).

thf('164',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_B ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['157','163'])).

thf('165',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['27','48'])).

thf('166',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('167',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('168',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('169',plain,
    ( ( ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['156','169'])).

thf('171',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( ( sk_B = sk_C_1 )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['155','172'])).

thf('174',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( sk_B = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_tarski @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('177',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
      = ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['74'])).

thf('179',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('181',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ~ ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['182'])).

thf('184',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['181','183'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('185',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('188',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('189',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['186','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['192'])).

thf('194',plain,(
    m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['178','193'])).

thf('195',plain,
    ( ( m1_subset_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['177','194'])).

thf('196',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r7_relat_2 @ ( u1_orders_2 @ X6 ) @ X5 )
      | ( v6_orders_2 @ X5 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('197',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( sk_B = sk_C_1 )
      | ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['174','199'])).

thf('201',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
      = ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('202',plain,
    ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
   <= ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['182'])).

thf('203',plain,
    ( ( ~ ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['200','203'])).

thf('205',plain,
    ( ( ( sk_B = sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('207',plain,
    ( ( ( sk_B = sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['187','188'])).

thf('209',plain,
    ( ( ( sk_B = sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( sk_B = sk_C_1 )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,
    ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
   <= ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['182'])).

thf('213',plain,
    ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B ) @ sk_A )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','213'])).

thf('215',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('216',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['187','188'])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['182'])).

thf('222',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X10 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('223',plain,(
    ! [X7: $i,X10: $i] :
      ( r2_hidden @ X10 @ ( k2_tarski @ X10 @ X7 ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('225',plain,(
    ! [X7: $i,X10: $i] :
      ( r2_hidden @ X7 @ ( k2_tarski @ X10 @ X7 ) ) ),
    inference(simplify,[status(thm)],['224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('227',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
      = ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('228',plain,
    ( ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['228'])).

thf('230',plain,
    ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['74'])).

thf('231',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v6_orders_2 @ X5 @ X6 )
      | ( r7_relat_2 @ ( u1_orders_2 @ X6 ) @ X5 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('232',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) )
      | ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) )
      | ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) )
   <= ( ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['229','234'])).

thf('236',plain,(
    m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['192'])).

thf('237',plain,
    ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['235','236'])).

thf('238',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['227','237'])).

thf('239',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r7_relat_2 @ X14 @ X15 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X14 )
      | ~ ( r2_hidden @ X17 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('240',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C_1 ) )
        | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
        | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C_1 ) )
        | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
        | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_B @ sk_C_1 ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['226','240'])).

thf('242',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C_1 ) )
        | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
        | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_B @ sk_C_1 ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C_1 ) )
        | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
        | ( r2_hidden @ ( k4_tarski @ X0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['225','243'])).

thf('245',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['223','244'])).

thf('246',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( u1_orders_2 @ X19 ) )
      | ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('247',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['247','248','249','250'])).

thf('252',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( u1_orders_2 @ X19 ) )
      | ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('253',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['253','254','255','256'])).

thf('258',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( r3_orders_2 @ X31 @ X30 @ X32 )
      | ~ ( r1_orders_2 @ X31 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('260',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['260','261','262'])).

thf('264',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['257','263'])).

thf('265',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['264','265'])).

thf('267',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('268',plain,
    ( ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
    | ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('269',plain,(
    ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['1','192','268'])).

thf('270',plain,(
    ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['267','269'])).

thf('271',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['266','270'])).

thf('272',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['271','272'])).

thf('274',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( r3_orders_2 @ X31 @ X30 @ X32 )
      | ~ ( r1_orders_2 @ X31 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('280',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['273','279'])).

thf('281',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['280','281'])).

thf('283',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('285',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['182'])).

thf('286',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('287',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('288',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['187','188'])).

thf('290',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,
    ( ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','69'])).

thf('294',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('295',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('296',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('297',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['74'])).

thf('298',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('299',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['299','300'])).

thf('302',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['301','302'])).

thf('304',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('306',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['304','305'])).

thf('307',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['303','306'])).

thf('308',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X0 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('309',plain,
    ( ( ( ( sk_D_1 @ ( k2_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['307','308'])).

thf('310',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('311',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('312',plain,
    ( ( ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['309','310','311'])).

thf('313',plain,
    ( ( ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['312'])).

thf('314',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['296','313'])).

thf('315',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,
    ( ( ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['314','315'])).

thf('317',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('318',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('319',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X14 ) @ ( sk_D_1 @ X13 @ X14 ) ) @ X14 )
      | ( r7_relat_2 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('320',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ ( k2_tarski @ X2 @ X0 ) @ X1 ) ) @ X1 )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X2 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['318','319'])).

thf('321',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ ( k2_tarski @ X2 @ X0 ) @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X0 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['317','321'])).

thf('323',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_B ) )
      | ( ( sk_C @ ( k2_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['316','322'])).

thf('324',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['27','48'])).

thf('325',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('326',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('327',plain,
    ( ( ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['323','324','325','326'])).

thf('328',plain,
    ( ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['327'])).

thf('329',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['295','328'])).

thf('330',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ( ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['329','330'])).

thf('332',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('333',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('334',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X14 ) @ ( sk_D_1 @ X13 @ X14 ) ) @ X14 )
      | ( r7_relat_2 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('335',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ X1 ) @ X0 ) @ X1 )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['333','334'])).

thf('336',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ X1 ) @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['335'])).

thf('337',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 ) @ X0 ) @ X2 )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X1 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['332','336'])).

thf('338',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_B ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['331','337'])).

thf('339',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['116','132'])).

thf('340',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('341',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('342',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['338','339','340','341'])).

thf('343',plain,
    ( ( ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['342'])).

thf('344',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['294','343'])).

thf('345',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['344','345'])).

thf('347',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('348',plain,
    ( ( ( ( sk_C @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['329','330'])).

thf('349',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('350',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_D_1 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('351',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X14 ) @ ( sk_C @ X13 @ X14 ) ) @ X14 )
      | ( r7_relat_2 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('352',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k2_tarski @ X2 @ X0 ) @ X1 ) ) @ X1 )
      | ( ( sk_D_1 @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X2 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['350','351'])).

thf('353',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k2_tarski @ X2 @ X0 ) @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['352'])).

thf('354',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ( ( sk_D_1 @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X0 )
      | ( r7_relat_2 @ X2 @ ( k2_tarski @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['349','353'])).

thf('355',plain,
    ( ( ~ ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_B ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['348','354'])).

thf('356',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['303','306'])).

thf('357',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('358',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('359',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['355','356','357','358'])).

thf('360',plain,
    ( ( ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['359'])).

thf('361',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['347','360'])).

thf('362',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( ( sk_D_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
        = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['361','362'])).

thf('364',plain,
    ( ( ( sk_B = sk_C_1 )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['346','363'])).

thf('365',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( sk_B = sk_C_1 ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['364'])).

thf('366',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('367',plain,
    ( ( ( sk_B = sk_C_1 )
      | ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['365','366'])).

thf('368',plain,
    ( ( ~ ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('369',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['367','368'])).

thf('370',plain,
    ( ( ( sk_B = sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['369'])).

thf('371',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('372',plain,
    ( ( ( sk_B = sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['370','371'])).

thf('373',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['187','188'])).

thf('374',plain,
    ( ( ( sk_B = sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['372','373'])).

thf('375',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,
    ( ( sk_B = sk_C_1 )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['374','375'])).

thf('377',plain,
    ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
   <= ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['182'])).

thf('378',plain,
    ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B ) @ sk_A )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['376','377'])).

thf('379',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['293','378'])).

thf('380',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('381',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['379','380'])).

thf('382',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['187','188'])).

thf('383',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
      & ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['381','382'])).

thf('384',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['383','384'])).

thf('386',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
    | ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['228'])).

thf('387',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','220','221','192','292','385','386'])).


%------------------------------------------------------------------------------
