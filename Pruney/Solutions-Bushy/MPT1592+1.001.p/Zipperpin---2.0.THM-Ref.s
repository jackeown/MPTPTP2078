%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1592+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IwSBeucJKf

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:51 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 557 expanded)
%              Number of leaves         :   42 ( 177 expanded)
%              Depth                    :   26
%              Number of atoms          : 1812 (14540 expanded)
%              Number of equality atoms :   47 ( 771 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v4_yellow_0_type,type,(
    v4_yellow_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v6_yellow_0_type,type,(
    v6_yellow_0: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k7_domain_1_type,type,(
    k7_domain_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(t71_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_yellow_0 @ B @ A )
            & ( v6_yellow_0 @ B @ A )
            & ( m1_yellow_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                         => ( ( ( E = C )
                              & ( F = D ) )
                           => ( ( k13_lattice3 @ B @ C @ D )
                              = ( k13_lattice3 @ A @ E @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_yellow_0 @ B @ A )
              & ( v6_yellow_0 @ B @ A )
              & ( m1_yellow_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                           => ( ( ( E = C )
                                & ( F = D ) )
                             => ( ( k13_lattice3 @ B @ C @ D )
                                = ( k13_lattice3 @ A @ E @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_yellow_0])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( ( k7_domain_1 @ A @ B @ C )
        = ( k2_tarski @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( ( k7_domain_1 @ X21 @ X20 @ X22 )
        = ( k2_tarski @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_domain_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 )
        = ( k2_tarski @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ sk_D_1 )
      = ( k2_tarski @ sk_C_2 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( m1_subset_1 @ ( k7_domain_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k7_domain_1 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_domain_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_F = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_E = sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( ( k7_domain_1 @ X21 @ X20 @ X22 )
        = ( k2_tarski @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_domain_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ X0 )
        = ( k2_tarski @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ sk_D_1 )
      = ( k2_tarski @ sk_C_2 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf(d17_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( ( v6_yellow_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) )
                        & ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                        & ( r1_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ C @ D ) ) )
                     => ( r2_hidden @ ( k1_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_yellow_0 @ X9 @ X10 )
      | ~ ( v6_yellow_0 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ ( k1_yellow_0 @ X10 @ ( k7_domain_1 @ ( u1_struct_0 @ X10 ) @ X12 @ X11 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_yellow_0 @ X10 @ ( k7_domain_1 @ ( u1_struct_0 @ X10 ) @ X12 @ X11 ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_yellow_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C_2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ sk_D_1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v6_yellow_0 @ X0 @ sk_A )
      | ~ ( m1_yellow_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t20_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v1_lattice3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( r1_yellow_0 @ A @ ( k2_tarski @ B @ C ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_lattice3 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ( r1_yellow_0 @ X23 @ ( k2_tarski @ X25 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t20_yellow_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_tarski @ X0 @ sk_D_1 ) )
      | ~ ( v1_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_tarski @ X0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    r1_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_C_2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ sk_D_1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v6_yellow_0 @ X0 @ sk_A )
      | ~ ( m1_yellow_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','38','39','40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t41_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k1_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                = ( k13_lattice3 @ A @ B @ C ) ) ) ) ) )).

thf('45',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( ( k1_yellow_0 @ X29 @ ( k7_domain_1 @ ( u1_struct_0 @ X29 ) @ X28 @ X30 ) )
        = ( k13_lattice3 @ X29 @ X28 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v1_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t41_yellow_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ X0 ) )
        = ( k13_lattice3 @ sk_A @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ X0 ) )
        = ( k13_lattice3 @ sk_A @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50','51'])).

thf('53',plain,
    ( ( k1_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ sk_D_1 ) )
    = ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_C_2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v6_yellow_0 @ X0 @ sk_A )
      | ~ ( m1_yellow_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_yellow_0 @ sk_B_1 @ sk_A )
    | ~ ( v6_yellow_0 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','54'])).

thf('56',plain,(
    m1_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v6_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','58'])).

thf('60',plain,
    ( ( r2_hidden @ ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ sk_D_1 )
      = ( k2_tarski @ sk_C_2 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('62',plain,
    ( ( k1_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ sk_D_1 ) )
    = ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('63',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
      = ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('65',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
      = ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('67',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
      = ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('71',plain,(
    ! [X2: $i] :
      ( ~ ( v1_lattice3 @ X2 )
      | ~ ( v2_struct_0 @ X2 )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('72',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
    = ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['69','74'])).

thf(t65_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_yellow_0 @ B @ A )
            & ( m1_yellow_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( ( r1_yellow_0 @ A @ C )
                  & ( r2_hidden @ ( k1_yellow_0 @ A @ C ) @ ( u1_struct_0 @ B ) ) )
               => ( ( r1_yellow_0 @ B @ C )
                  & ( ( k1_yellow_0 @ B @ C )
                    = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf('76',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v4_yellow_0 @ X31 @ X32 )
      | ~ ( m1_yellow_0 @ X31 @ X32 )
      | ~ ( r1_yellow_0 @ X32 @ X33 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X32 @ X33 ) @ ( u1_struct_0 @ X31 ) )
      | ( ( k1_yellow_0 @ X31 @ X33 )
        = ( k1_yellow_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_yellow_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k1_yellow_0 @ X0 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
        = ( k1_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
      | ~ ( m1_yellow_0 @ X0 @ sk_A )
      | ~ ( v4_yellow_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k1_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
    = ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['69','74'])).

thf('81',plain,(
    r1_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k1_yellow_0 @ X0 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
        = ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) )
      | ~ ( m1_yellow_0 @ X0 @ sk_A )
      | ~ ( v4_yellow_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v4_yellow_0 @ sk_B_1 @ sk_A )
    | ~ ( m1_yellow_0 @ sk_B_1 @ sk_A )
    | ( ( k1_yellow_0 @ sk_B_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
      = ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','82'])).

thf('84',plain,(
    v4_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ sk_D_1 )
      = ( k2_tarski @ sk_C_2 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('87',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( ( k1_yellow_0 @ X29 @ ( k7_domain_1 @ ( u1_struct_0 @ X29 ) @ X28 @ X30 ) )
        = ( k13_lattice3 @ X29 @ X28 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v1_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t41_yellow_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v1_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k1_yellow_0 @ sk_B_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 ) )
        = ( k13_lattice3 @ sk_B_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( ( v4_yellow_0 @ B @ A )
           => ( ( v3_orders_2 @ B )
              & ( v4_yellow_0 @ B @ A ) ) ) ) ) )).

thf('92',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_yellow_0 @ X3 @ X4 )
      | ( v3_orders_2 @ X3 )
      | ~ ( v4_yellow_0 @ X3 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc6_yellow_0])).

thf('93',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v4_yellow_0 @ sk_B_1 @ sk_A )
    | ( v3_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v4_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v3_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    m1_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc7_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( ( v4_yellow_0 @ B @ A )
           => ( ( v4_orders_2 @ B )
              & ( v4_yellow_0 @ B @ A ) ) ) ) ) )).

thf('99',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_yellow_0 @ X5 @ X6 )
      | ( v4_orders_2 @ X5 )
      | ~ ( v4_yellow_0 @ X5 @ X6 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc7_yellow_0])).

thf('100',plain,
    ( ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v4_yellow_0 @ sk_B_1 @ sk_A )
    | ( v4_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v4_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,(
    m1_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc8_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( ( v4_yellow_0 @ B @ A )
           => ( ( v5_orders_2 @ B )
              & ( v4_yellow_0 @ B @ A ) ) ) ) ) )).

thf('106',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_yellow_0 @ X7 @ X8 )
      | ( v5_orders_2 @ X7 )
      | ~ ( v4_yellow_0 @ X7 @ X8 )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc8_yellow_0])).

thf('107',plain,
    ( ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v4_yellow_0 @ sk_B_1 @ sk_A )
    | ( v5_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v4_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v5_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,(
    m1_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc12_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v4_yellow_0 @ B @ A )
              & ( v6_yellow_0 @ B @ A ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v1_lattice3 @ B )
              & ( v4_yellow_0 @ B @ A )
              & ( v6_yellow_0 @ B @ A ) ) ) ) ) )).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_yellow_0 @ X0 @ X1 )
      | ( v1_lattice3 @ X0 )
      | ~ ( v6_yellow_0 @ X0 @ X1 )
      | ~ ( v4_yellow_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v1_lattice3 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc12_yellow_0])).

thf('114',plain,
    ( ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v4_yellow_0 @ sk_B_1 @ sk_A )
    | ~ ( v6_yellow_0 @ sk_B_1 @ sk_A )
    | ( v1_lattice3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v4_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v6_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_lattice3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_lattice3 @ sk_B_1 ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    m1_yellow_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('125',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_yellow_0 @ X17 @ X18 )
      | ( l1_orders_2 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_0])).

thf('126',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k1_yellow_0 @ sk_B_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 ) )
        = ( k13_lattice3 @ sk_B_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','97','104','111','123','128'])).

thf('130',plain,
    ( ( k1_yellow_0 @ sk_B_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ sk_D_1 ) )
    = ( k13_lattice3 @ sk_B_1 @ sk_C_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['87','129'])).

thf('131',plain,
    ( ( ( k1_yellow_0 @ sk_B_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
      = ( k13_lattice3 @ sk_B_1 @ sk_C_2 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['86','130'])).

thf('132',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('133',plain,
    ( ( ( k1_yellow_0 @ sk_B_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
      = ( k13_lattice3 @ sk_B_1 @ sk_C_2 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['126','127'])).

thf('135',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('136',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k1_yellow_0 @ sk_B_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
      = ( k13_lattice3 @ sk_B_1 @ sk_C_2 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['133','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k1_yellow_0 @ sk_B_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) )
    = ( k13_lattice3 @ sk_B_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( k13_lattice3 @ sk_B_1 @ sk_C_2 @ sk_D_1 )
      = ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85','139'])).

thf('141',plain,
    ( ~ ( m1_subset_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( ( k13_lattice3 @ sk_B_1 @ sk_C_2 @ sk_D_1 )
      = ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ( k13_lattice3 @ sk_B_1 @ sk_C_2 @ sk_D_1 )
 != ( k13_lattice3 @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    sk_E = sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    sk_F = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ( k13_lattice3 @ sk_B_1 @ sk_C_2 @ sk_D_1 )
 != ( k13_lattice3 @ sk_A @ sk_C_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ~ ( m1_subset_1 @ ( k2_tarski @ sk_C_2 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['141','145'])).

thf('147',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','146'])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('150',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['66','67'])).

thf('152',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('157',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['134','135'])).

thf('161',plain,(
    v2_struct_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    $false ),
    inference(demod,[status(thm)],['0','161'])).


%------------------------------------------------------------------------------
