%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZgIHXSP2my

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:46 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 601 expanded)
%              Number of leaves         :   36 ( 177 expanded)
%              Depth                    :   39
%              Number of atoms          : 3355 (20610 expanded)
%              Number of equality atoms :   85 ( 665 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(t52_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ! [D: $i] :
                      ( ( ( v1_finset_1 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r1_yellow_0 @ A @ D ) ) )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r2_hidden @ D @ C )
                          & ! [E: $i] :
                              ( ( ( v1_finset_1 @ E )
                                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
                             => ~ ( ( r1_yellow_0 @ A @ E )
                                  & ( D
                                    = ( k1_yellow_0 @ A @ E ) ) ) ) ) )
                  & ! [D: $i] :
                      ( ( ( v1_finset_1 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                    <=> ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ! [D: $i] :
                        ( ( ( v1_finset_1 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                       => ( ( D != k1_xboole_0 )
                         => ( r1_yellow_0 @ A @ D ) ) )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ~ ( ( r2_hidden @ D @ C )
                            & ! [E: $i] :
                                ( ( ( v1_finset_1 @ E )
                                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
                               => ~ ( ( r1_yellow_0 @ A @ E )
                                    & ( D
                                      = ( k1_yellow_0 @ A @ E ) ) ) ) ) )
                    & ! [D: $i] :
                        ( ( ( v1_finset_1 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                       => ( ( D != k1_xboole_0 )
                         => ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ B @ D )
                      <=> ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_waybel_0])).

thf('0',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X11 @ X10 ) @ X11 )
      | ( r2_lattice3 @ X10 @ X11 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ( r2_lattice3 @ X10 @ X11 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X25: $i] :
      ( ( X25
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X25 ) ) )
      | ~ ( r2_hidden @ X25 @ sk_C )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('18',plain,(
    ! [X25: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X25 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X25 @ sk_C )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_tarski @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ C @ D )
                 => ( r1_lattice3 @ A @ B @ D ) )
                & ( ( r2_lattice3 @ A @ C @ D )
                 => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r2_lattice3 @ X22 @ X21 @ X23 )
      | ( r2_lattice3 @ X22 @ X20 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('35',plain,(
    ! [X25: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X25 ) )
      | ~ ( r2_hidden @ X25 @ sk_C )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('40',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(d9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ B )
           => ( ( C
                = ( k1_yellow_0 @ A @ B ) )
            <=> ( ( r2_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k1_yellow_0 @ X13 @ X14 ) )
      | ~ ( r2_lattice3 @ X13 @ X14 @ X16 )
      | ( r1_orders_2 @ X13 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_yellow_0 @ X13 @ X14 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( r1_yellow_0 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ ( k1_yellow_0 @ X13 @ X14 ) @ X16 )
      | ~ ( r2_lattice3 @ X13 @ X14 @ X16 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['32','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['15','53'])).

thf('55',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_orders_2 @ X10 @ ( sk_D @ X9 @ X11 @ X10 ) @ X9 )
      | ( r2_lattice3 @ X10 @ X11 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(clc,[status(thm)],['55','60'])).

thf('62',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('67',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(fc1_finset_1,axiom,(
    ! [A: $i] :
      ( v1_finset_1 @ ( k1_tarski @ A ) ) )).

thf('71',plain,(
    ! [X6: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('72',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t24_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ B @ B ) ) ) )).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ X7 @ X7 )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_orders_2])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t7_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B )
                 => ( r1_orders_2 @ A @ B @ C ) )
                & ( ( r1_orders_2 @ A @ B @ C )
                 => ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) )
                & ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B )
                 => ( r1_orders_2 @ A @ C @ B ) )
                & ( ( r1_orders_2 @ A @ C @ B )
                 => ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_orders_2 @ X18 @ X19 @ X17 )
      | ( r2_lattice3 @ X18 @ ( k1_tarski @ X19 ) @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X1 ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X1 ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('92',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('95',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_lattice3 @ X13 @ X14 @ X15 )
      | ( r2_lattice3 @ X13 @ X14 @ ( sk_D_1 @ X15 @ X14 @ X13 ) )
      | ( X15
        = ( k1_yellow_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_yellow_0 @ X13 @ X14 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( r2_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( r2_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['92','100'])).

thf('102',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('106',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_lattice3 @ X13 @ X14 @ X15 )
      | ( m1_subset_1 @ ( sk_D_1 @ X15 @ X14 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( X15
        = ( k1_yellow_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_yellow_0 @ X13 @ X14 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['103','111'])).

thf('113',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_lattice3 @ X18 @ ( k1_tarski @ X19 ) @ X17 )
      | ( r1_orders_2 @ X18 @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','117'])).

thf('119',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','119'])).

thf('121',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_lattice3 @ X13 @ X14 @ X15 )
      | ~ ( r1_orders_2 @ X13 @ X15 @ ( sk_D_1 @ X15 @ X14 @ X13 ) )
      | ( X15
        = ( k1_yellow_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_yellow_0 @ X13 @ X14 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('123',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','126'])).

thf('128',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','128'])).

thf('130',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['72','130'])).

thf('132',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('134',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X24 ) @ sk_C )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X6: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('137',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('139',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( k1_tarski @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('141',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('144',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_C )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,
    ( ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['132','145'])).

thf('147',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_lattice3 @ X18 @ ( k1_tarski @ X19 ) @ X17 )
      | ( r1_orders_2 @ X18 @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['65','153'])).

thf('155',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('157',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['155','156'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('158',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('159',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('160',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('161',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('163',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','63','64','163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZgIHXSP2my
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:56:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.82/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.01  % Solved by: fo/fo7.sh
% 0.82/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.01  % done 629 iterations in 0.552s
% 0.82/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.01  % SZS output start Refutation
% 0.82/1.01  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.82/1.01  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.82/1.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.82/1.01  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.82/1.01  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.82/1.01  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.82/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.01  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.82/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.82/1.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.82/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.01  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.82/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.01  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.82/1.01  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.82/1.01  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.82/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/1.01  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.82/1.01  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.82/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.82/1.01  thf(sk_E_type, type, sk_E: $i > $i).
% 0.82/1.01  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.82/1.01  thf(t52_waybel_0, conjecture,
% 0.82/1.01    (![A:$i]:
% 0.82/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.82/1.01         ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.82/1.01       ( ![B:$i]:
% 0.82/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.01           ( ![C:$i]:
% 0.82/1.01             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.01               ( ( ( ![D:$i]:
% 0.82/1.01                     ( ( ( v1_finset_1 @ D ) & 
% 0.82/1.01                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.82/1.01                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.82/1.01                         ( r1_yellow_0 @ A @ D ) ) ) ) & 
% 0.82/1.01                   ( ![D:$i]:
% 0.82/1.01                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01                       ( ~( ( r2_hidden @ D @ C ) & 
% 0.82/1.01                            ( ![E:$i]:
% 0.82/1.01                              ( ( ( v1_finset_1 @ E ) & 
% 0.82/1.01                                  ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.82/1.01                                ( ~( ( r1_yellow_0 @ A @ E ) & 
% 0.82/1.01                                     ( ( D ) = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.82/1.01                   ( ![D:$i]:
% 0.82/1.01                     ( ( ( v1_finset_1 @ D ) & 
% 0.82/1.01                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.82/1.01                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.82/1.01                         ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.82/1.01                 ( ![D:$i]:
% 0.82/1.01                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01                     ( ( r2_lattice3 @ A @ B @ D ) <=>
% 0.82/1.01                       ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.82/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.01    (~( ![A:$i]:
% 0.82/1.01        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.82/1.01            ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.82/1.01          ( ![B:$i]:
% 0.82/1.01            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.01              ( ![C:$i]:
% 0.82/1.01                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.01                  ( ( ( ![D:$i]:
% 0.82/1.01                        ( ( ( v1_finset_1 @ D ) & 
% 0.82/1.01                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.82/1.01                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.82/1.01                            ( r1_yellow_0 @ A @ D ) ) ) ) & 
% 0.82/1.01                      ( ![D:$i]:
% 0.82/1.01                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01                          ( ~( ( r2_hidden @ D @ C ) & 
% 0.82/1.01                               ( ![E:$i]:
% 0.82/1.01                                 ( ( ( v1_finset_1 @ E ) & 
% 0.82/1.01                                     ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.82/1.01                                   ( ~( ( r1_yellow_0 @ A @ E ) & 
% 0.82/1.01                                        ( ( D ) = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.82/1.01                      ( ![D:$i]:
% 0.82/1.01                        ( ( ( v1_finset_1 @ D ) & 
% 0.82/1.01                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.82/1.01                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.82/1.01                            ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.82/1.01                    ( ![D:$i]:
% 0.82/1.01                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01                        ( ( r2_lattice3 @ A @ B @ D ) <=>
% 0.82/1.01                          ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.82/1.01    inference('cnf.neg', [status(esa)], [t52_waybel_0])).
% 0.82/1.01  thf('0', plain,
% 0.82/1.01      ((~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01        | ~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('1', plain,
% 0.82/1.01      (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.82/1.01       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.82/1.01      inference('split', [status(esa)], ['0'])).
% 0.82/1.01  thf('2', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf(d9_lattice3, axiom,
% 0.82/1.01    (![A:$i]:
% 0.82/1.01     ( ( l1_orders_2 @ A ) =>
% 0.82/1.01       ( ![B:$i,C:$i]:
% 0.82/1.01         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.82/1.01             ( ![D:$i]:
% 0.82/1.01               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.82/1.01  thf('3', plain,
% 0.82/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.82/1.01         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X9 @ X11 @ X10) @ X11)
% 0.82/1.01          | (r2_lattice3 @ X10 @ X11 @ X9)
% 0.82/1.01          | ~ (l1_orders_2 @ X10))),
% 0.82/1.01      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.82/1.01  thf('4', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (l1_orders_2 @ sk_A)
% 0.82/1.01          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['2', '3'])).
% 0.82/1.01  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('6', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.82/1.01      inference('demod', [status(thm)], ['4', '5'])).
% 0.82/1.01  thf('7', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('8', plain,
% 0.82/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.82/1.01         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ X9 @ X11 @ X10) @ (u1_struct_0 @ X10))
% 0.82/1.01          | (r2_lattice3 @ X10 @ X11 @ X9)
% 0.82/1.01          | ~ (l1_orders_2 @ X10))),
% 0.82/1.01      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.82/1.01  thf('9', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (l1_orders_2 @ sk_A)
% 0.82/1.01          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['7', '8'])).
% 0.82/1.01  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('11', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('12', plain,
% 0.82/1.01      (![X25 : $i]:
% 0.82/1.01         (((X25) = (k1_yellow_0 @ sk_A @ (sk_E @ X25)))
% 0.82/1.01          | ~ (r2_hidden @ X25 @ sk_C)
% 0.82/1.01          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('13', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.82/1.01          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.82/1.01              = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)))))),
% 0.82/1.01      inference('sup-', [status(thm)], ['11', '12'])).
% 0.82/1.01  thf('14', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.82/1.01            = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.82/1.01        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.82/1.01      inference('sup-', [status(thm)], ['6', '13'])).
% 0.82/1.01  thf('15', plain,
% 0.82/1.01      ((((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.82/1.01          = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.82/1.01        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.82/1.01      inference('simplify', [status(thm)], ['14'])).
% 0.82/1.01  thf('16', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.82/1.01      inference('demod', [status(thm)], ['4', '5'])).
% 0.82/1.01  thf('17', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('18', plain,
% 0.82/1.01      (![X25 : $i]:
% 0.82/1.01         ((m1_subset_1 @ (sk_E @ X25) @ (k1_zfmisc_1 @ sk_B))
% 0.82/1.01          | ~ (r2_hidden @ X25 @ sk_C)
% 0.82/1.01          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('19', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.82/1.01          | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.82/1.01             (k1_zfmisc_1 @ sk_B)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.01  thf('20', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01        | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.82/1.01           (k1_zfmisc_1 @ sk_B))
% 0.82/1.01        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.82/1.01      inference('sup-', [status(thm)], ['16', '19'])).
% 0.82/1.01  thf('21', plain,
% 0.82/1.01      (((m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.82/1.01         (k1_zfmisc_1 @ sk_B))
% 0.82/1.01        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.82/1.01      inference('simplify', [status(thm)], ['20'])).
% 0.82/1.01  thf(t3_subset, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.82/1.01  thf('22', plain,
% 0.82/1.01      (![X3 : $i, X4 : $i]:
% 0.82/1.01         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.82/1.01  thf('23', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01        | (r1_tarski @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_B))),
% 0.82/1.01      inference('sup-', [status(thm)], ['21', '22'])).
% 0.82/1.01  thf('24', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('25', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.82/1.01         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.82/1.01      inference('split', [status(esa)], ['24'])).
% 0.82/1.01  thf('26', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf(t9_yellow_0, axiom,
% 0.82/1.01    (![A:$i]:
% 0.82/1.01     ( ( l1_orders_2 @ A ) =>
% 0.82/1.01       ( ![B:$i,C:$i]:
% 0.82/1.01         ( ( r1_tarski @ B @ C ) =>
% 0.82/1.01           ( ![D:$i]:
% 0.82/1.01             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.82/1.01                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.82/1.01  thf('27', plain,
% 0.82/1.01      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.82/1.01         (~ (r1_tarski @ X20 @ X21)
% 0.82/1.01          | ~ (r2_lattice3 @ X22 @ X21 @ X23)
% 0.82/1.01          | (r2_lattice3 @ X22 @ X20 @ X23)
% 0.82/1.01          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.82/1.01          | ~ (l1_orders_2 @ X22))),
% 0.82/1.01      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.82/1.01  thf('28', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (l1_orders_2 @ sk_A)
% 0.82/1.01          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.82/1.01          | ~ (r1_tarski @ X0 @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['26', '27'])).
% 0.82/1.01  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('30', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.82/1.01          | ~ (r1_tarski @ X0 @ X1))),
% 0.82/1.01      inference('demod', [status(thm)], ['28', '29'])).
% 0.82/1.01  thf('31', plain,
% 0.82/1.01      ((![X0 : $i]:
% 0.82/1.01          (~ (r1_tarski @ X0 @ sk_B) | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 0.82/1.01         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['25', '30'])).
% 0.82/1.01  thf('32', plain,
% 0.82/1.01      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01         | (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.82/1.01            sk_D_2)))
% 0.82/1.01         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['23', '31'])).
% 0.82/1.01  thf('33', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.82/1.01      inference('demod', [status(thm)], ['4', '5'])).
% 0.82/1.01  thf('34', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('35', plain,
% 0.82/1.01      (![X25 : $i]:
% 0.82/1.01         ((r1_yellow_0 @ sk_A @ (sk_E @ X25))
% 0.82/1.01          | ~ (r2_hidden @ X25 @ sk_C)
% 0.82/1.01          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('36', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.82/1.01          | (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A))))),
% 0.82/1.01      inference('sup-', [status(thm)], ['34', '35'])).
% 0.82/1.01  thf('37', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01        | (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.82/1.01        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.82/1.01      inference('sup-', [status(thm)], ['33', '36'])).
% 0.82/1.01  thf('38', plain,
% 0.82/1.01      (((r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.82/1.01        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.82/1.01      inference('simplify', [status(thm)], ['37'])).
% 0.82/1.01  thf('39', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('40', plain,
% 0.82/1.01      ((((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.82/1.01          = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.82/1.01        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.82/1.01      inference('simplify', [status(thm)], ['14'])).
% 0.82/1.01  thf(d9_yellow_0, axiom,
% 0.82/1.01    (![A:$i]:
% 0.82/1.01     ( ( l1_orders_2 @ A ) =>
% 0.82/1.01       ( ![B:$i,C:$i]:
% 0.82/1.01         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01           ( ( r1_yellow_0 @ A @ B ) =>
% 0.82/1.01             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.82/1.01               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.82/1.01                 ( ![D:$i]:
% 0.82/1.01                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.82/1.01                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.82/1.01  thf('41', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.82/1.01         (((X15) != (k1_yellow_0 @ X13 @ X14))
% 0.82/1.01          | ~ (r2_lattice3 @ X13 @ X14 @ X16)
% 0.82/1.01          | (r1_orders_2 @ X13 @ X15 @ X16)
% 0.82/1.01          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.82/1.01          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.82/1.01          | ~ (r1_yellow_0 @ X13 @ X14)
% 0.82/1.01          | ~ (l1_orders_2 @ X13))),
% 0.82/1.01      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.82/1.01  thf('42', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.82/1.01         (~ (l1_orders_2 @ X13)
% 0.82/1.01          | ~ (r1_yellow_0 @ X13 @ X14)
% 0.82/1.01          | ~ (m1_subset_1 @ (k1_yellow_0 @ X13 @ X14) @ (u1_struct_0 @ X13))
% 0.82/1.01          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.82/1.01          | (r1_orders_2 @ X13 @ (k1_yellow_0 @ X13 @ X14) @ X16)
% 0.82/1.01          | ~ (r2_lattice3 @ X13 @ X14 @ X16))),
% 0.82/1.01      inference('simplify', [status(thm)], ['41'])).
% 0.82/1.01  thf('43', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.82/1.01          | (r1_orders_2 @ sk_A @ 
% 0.82/1.01             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 0.82/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.82/1.01          | ~ (l1_orders_2 @ sk_A))),
% 0.82/1.01      inference('sup-', [status(thm)], ['40', '42'])).
% 0.82/1.01  thf('44', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('45', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.82/1.01          | (r1_orders_2 @ sk_A @ 
% 0.82/1.01             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 0.82/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))),
% 0.82/1.01      inference('demod', [status(thm)], ['43', '44'])).
% 0.82/1.01  thf('46', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.82/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | (r1_orders_2 @ sk_A @ 
% 0.82/1.01             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 0.82/1.01          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.82/1.01          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.82/1.01      inference('sup-', [status(thm)], ['39', '45'])).
% 0.82/1.01  thf('47', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.82/1.01          | (r1_orders_2 @ sk_A @ 
% 0.82/1.01             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 0.82/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.82/1.01          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.82/1.01      inference('simplify', [status(thm)], ['46'])).
% 0.82/1.01  thf('48', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | (r1_orders_2 @ sk_A @ 
% 0.82/1.01             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 0.82/1.01          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['38', '47'])).
% 0.82/1.01  thf('49', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.82/1.01          | (r1_orders_2 @ sk_A @ 
% 0.82/1.01             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 0.82/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.82/1.01      inference('simplify', [status(thm)], ['48'])).
% 0.82/1.01  thf('50', plain,
% 0.82/1.01      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01         | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))
% 0.82/1.01         | (r1_orders_2 @ sk_A @ 
% 0.82/1.01            (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 0.82/1.01            sk_D_2)))
% 0.82/1.01         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['32', '49'])).
% 0.82/1.01  thf('51', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('52', plain,
% 0.82/1.01      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01         | (r1_orders_2 @ sk_A @ 
% 0.82/1.01            (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 0.82/1.01            sk_D_2)))
% 0.82/1.01         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.82/1.01      inference('demod', [status(thm)], ['50', '51'])).
% 0.82/1.01  thf('53', plain,
% 0.82/1.01      ((((r1_orders_2 @ sk_A @ 
% 0.82/1.01          (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 0.82/1.01          sk_D_2)
% 0.82/1.01         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.82/1.01         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['52'])).
% 0.82/1.01  thf('54', plain,
% 0.82/1.01      ((((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2)
% 0.82/1.01         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.82/1.01         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.82/1.01      inference('sup+', [status(thm)], ['15', '53'])).
% 0.82/1.01  thf('55', plain,
% 0.82/1.01      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.82/1.01         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2)))
% 0.82/1.01         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['54'])).
% 0.82/1.01  thf('56', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('57', plain,
% 0.82/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.82/1.01         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.82/1.01          | ~ (r1_orders_2 @ X10 @ (sk_D @ X9 @ X11 @ X10) @ X9)
% 0.82/1.01          | (r2_lattice3 @ X10 @ X11 @ X9)
% 0.82/1.01          | ~ (l1_orders_2 @ X10))),
% 0.82/1.01      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.82/1.01  thf('58', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (l1_orders_2 @ sk_A)
% 0.82/1.01          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.82/1.01      inference('sup-', [status(thm)], ['56', '57'])).
% 0.82/1.01  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('60', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.82/1.01      inference('demod', [status(thm)], ['58', '59'])).
% 0.82/1.01  thf('61', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.82/1.01         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.82/1.01      inference('clc', [status(thm)], ['55', '60'])).
% 0.82/1.01  thf('62', plain,
% 0.82/1.01      ((~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.82/1.01         <= (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.01      inference('split', [status(esa)], ['0'])).
% 0.82/1.01  thf('63', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.82/1.01       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.82/1.01      inference('sup-', [status(thm)], ['61', '62'])).
% 0.82/1.01  thf('64', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.82/1.01       ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.82/1.01      inference('split', [status(esa)], ['24'])).
% 0.82/1.01  thf('65', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('66', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.82/1.01      inference('demod', [status(thm)], ['4', '5'])).
% 0.82/1.01  thf(t63_subset_1, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( r2_hidden @ A @ B ) =>
% 0.82/1.01       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.82/1.01  thf('67', plain,
% 0.82/1.01      (![X1 : $i, X2 : $i]:
% 0.82/1.01         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.82/1.01          | ~ (r2_hidden @ X1 @ X2))),
% 0.82/1.01      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.82/1.01  thf('68', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.82/1.01             (k1_zfmisc_1 @ X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['66', '67'])).
% 0.82/1.01  thf('69', plain,
% 0.82/1.01      (![X26 : $i]:
% 0.82/1.01         (((X26) = (k1_xboole_0))
% 0.82/1.01          | (r1_yellow_0 @ sk_A @ X26)
% 0.82/1.01          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ sk_B))
% 0.82/1.01          | ~ (v1_finset_1 @ X26))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('70', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.01        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.01        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.01        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['68', '69'])).
% 0.82/1.01  thf(fc1_finset_1, axiom, (![A:$i]: ( v1_finset_1 @ ( k1_tarski @ A ) ))).
% 0.82/1.01  thf('71', plain, (![X6 : $i]: (v1_finset_1 @ (k1_tarski @ X6))),
% 0.82/1.01      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.82/1.01  thf('72', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.01        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.01        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.82/1.01      inference('demod', [status(thm)], ['70', '71'])).
% 0.82/1.01  thf('73', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('74', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf(t24_orders_2, axiom,
% 0.82/1.01    (![A:$i]:
% 0.82/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.82/1.01       ( ![B:$i]:
% 0.82/1.01         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.82/1.01  thf('75', plain,
% 0.82/1.01      (![X7 : $i, X8 : $i]:
% 0.82/1.01         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.82/1.01          | (r1_orders_2 @ X8 @ X7 @ X7)
% 0.82/1.01          | ~ (l1_orders_2 @ X8)
% 0.82/1.01          | ~ (v3_orders_2 @ X8)
% 0.82/1.01          | (v2_struct_0 @ X8))),
% 0.82/1.01      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.82/1.01  thf('76', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (v2_struct_0 @ sk_A)
% 0.82/1.01          | ~ (v3_orders_2 @ sk_A)
% 0.82/1.01          | ~ (l1_orders_2 @ sk_A)
% 0.82/1.01          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.82/1.01             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['74', '75'])).
% 0.82/1.01  thf('77', plain, ((v3_orders_2 @ sk_A)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('78', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('79', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (v2_struct_0 @ sk_A)
% 0.82/1.01          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.82/1.01             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.82/1.01  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('81', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.82/1.01           (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.82/1.01          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.82/1.01      inference('clc', [status(thm)], ['79', '80'])).
% 0.82/1.01  thf('82', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf(t7_yellow_0, axiom,
% 0.82/1.01    (![A:$i]:
% 0.82/1.01     ( ( l1_orders_2 @ A ) =>
% 0.82/1.01       ( ![B:$i]:
% 0.82/1.01         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01           ( ![C:$i]:
% 0.82/1.01             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.01               ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.82/1.01                   ( r1_orders_2 @ A @ B @ C ) ) & 
% 0.82/1.01                 ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.82/1.01                   ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 0.82/1.01                 ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.82/1.01                   ( r1_orders_2 @ A @ C @ B ) ) & 
% 0.82/1.01                 ( ( r1_orders_2 @ A @ C @ B ) =>
% 0.82/1.01                   ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ))).
% 0.82/1.01  thf('83', plain,
% 0.82/1.01      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.82/1.01         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.82/1.01          | ~ (r1_orders_2 @ X18 @ X19 @ X17)
% 0.82/1.01          | (r2_lattice3 @ X18 @ (k1_tarski @ X19) @ X17)
% 0.82/1.01          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.82/1.01          | ~ (l1_orders_2 @ X18))),
% 0.82/1.01      inference('cnf', [status(esa)], [t7_yellow_0])).
% 0.82/1.01  thf('84', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | ~ (l1_orders_2 @ sk_A)
% 0.82/1.01          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | (r2_lattice3 @ sk_A @ (k1_tarski @ X1) @ 
% 0.82/1.01             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.82/1.01          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['82', '83'])).
% 0.82/1.01  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('86', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | (r2_lattice3 @ sk_A @ (k1_tarski @ X1) @ 
% 0.82/1.01             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.82/1.01          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['84', '85'])).
% 0.82/1.01  thf('87', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.82/1.01             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.82/1.01          | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.82/1.01      inference('sup-', [status(thm)], ['81', '86'])).
% 0.82/1.01  thf('88', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.01          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.82/1.01             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.82/1.01          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.82/1.01      inference('simplify', [status(thm)], ['87'])).
% 0.82/1.01  thf('89', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('90', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.82/1.01             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.82/1.01      inference('clc', [status(thm)], ['88', '89'])).
% 0.82/1.01  thf('91', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('92', plain,
% 0.82/1.01      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.01        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.01        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.82/1.01      inference('demod', [status(thm)], ['70', '71'])).
% 0.82/1.01  thf('93', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.82/1.01             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.82/1.01      inference('clc', [status(thm)], ['88', '89'])).
% 0.82/1.01  thf('94', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('95', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.82/1.01         (~ (r2_lattice3 @ X13 @ X14 @ X15)
% 0.82/1.01          | (r2_lattice3 @ X13 @ X14 @ (sk_D_1 @ X15 @ X14 @ X13))
% 0.82/1.01          | ((X15) = (k1_yellow_0 @ X13 @ X14))
% 0.82/1.01          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.82/1.01          | ~ (r1_yellow_0 @ X13 @ X14)
% 0.82/1.01          | ~ (l1_orders_2 @ X13))),
% 0.82/1.01      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.82/1.01  thf('96', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.01          | ~ (l1_orders_2 @ sk_A)
% 0.82/1.01          | ~ (r1_yellow_0 @ sk_A @ X1)
% 0.82/1.01          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 0.82/1.01          | (r2_lattice3 @ sk_A @ X1 @ 
% 0.82/1.01             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A))
% 0.82/1.01          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['94', '95'])).
% 0.82/1.02  thf('97', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('98', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]:
% 0.82/1.02         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | ~ (r1_yellow_0 @ sk_A @ X1)
% 0.82/1.02          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 0.82/1.02          | (r2_lattice3 @ sk_A @ X1 @ 
% 0.82/1.02             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A))
% 0.82/1.02          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.82/1.02      inference('demod', [status(thm)], ['96', '97'])).
% 0.82/1.02  thf('99', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.82/1.02             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.82/1.02              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A))
% 0.82/1.02          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.82/1.02              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 0.82/1.02          | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 0.82/1.02          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.82/1.02      inference('sup-', [status(thm)], ['93', '98'])).
% 0.82/1.02  thf('100', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         (~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 0.82/1.02          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.82/1.02              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 0.82/1.02          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.82/1.02             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.82/1.02              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A))
% 0.82/1.02          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.82/1.02      inference('simplify', [status(thm)], ['99'])).
% 0.82/1.02  thf('101', plain,
% 0.82/1.02      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.82/1.02           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.82/1.02      inference('sup-', [status(thm)], ['92', '100'])).
% 0.82/1.02  thf('102', plain,
% 0.82/1.02      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02          = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.82/1.02           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.82/1.02      inference('simplify', [status(thm)], ['101'])).
% 0.82/1.02  thf('103', plain,
% 0.82/1.02      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.82/1.02      inference('demod', [status(thm)], ['70', '71'])).
% 0.82/1.02  thf('104', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.82/1.02             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.82/1.02      inference('clc', [status(thm)], ['88', '89'])).
% 0.82/1.02  thf('105', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('demod', [status(thm)], ['9', '10'])).
% 0.82/1.02  thf('106', plain,
% 0.82/1.02      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.82/1.02         (~ (r2_lattice3 @ X13 @ X14 @ X15)
% 0.82/1.02          | (m1_subset_1 @ (sk_D_1 @ X15 @ X14 @ X13) @ (u1_struct_0 @ X13))
% 0.82/1.02          | ((X15) = (k1_yellow_0 @ X13 @ X14))
% 0.82/1.02          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.82/1.02          | ~ (r1_yellow_0 @ X13 @ X14)
% 0.82/1.02          | ~ (l1_orders_2 @ X13))),
% 0.82/1.02      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.82/1.02  thf('107', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]:
% 0.82/1.02         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | ~ (l1_orders_2 @ sk_A)
% 0.82/1.02          | ~ (r1_yellow_0 @ sk_A @ X1)
% 0.82/1.02          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 0.82/1.02          | (m1_subset_1 @ 
% 0.82/1.02             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A) @ 
% 0.82/1.02             (u1_struct_0 @ sk_A))
% 0.82/1.02          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['105', '106'])).
% 0.82/1.02  thf('108', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('109', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]:
% 0.82/1.02         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | ~ (r1_yellow_0 @ sk_A @ X1)
% 0.82/1.02          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 0.82/1.02          | (m1_subset_1 @ 
% 0.82/1.02             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A) @ 
% 0.82/1.02             (u1_struct_0 @ sk_A))
% 0.82/1.02          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.82/1.02      inference('demod', [status(thm)], ['107', '108'])).
% 0.82/1.02  thf('110', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | (m1_subset_1 @ 
% 0.82/1.02             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.82/1.02              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A) @ 
% 0.82/1.02             (u1_struct_0 @ sk_A))
% 0.82/1.02          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.82/1.02              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 0.82/1.02          | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 0.82/1.02          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.82/1.02      inference('sup-', [status(thm)], ['104', '109'])).
% 0.82/1.02  thf('111', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         (~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 0.82/1.02          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.82/1.02              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 0.82/1.02          | (m1_subset_1 @ 
% 0.82/1.02             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.82/1.02              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A) @ 
% 0.82/1.02             (u1_struct_0 @ sk_A))
% 0.82/1.02          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.82/1.02      inference('simplify', [status(thm)], ['110'])).
% 0.82/1.02  thf('112', plain,
% 0.82/1.02      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | (m1_subset_1 @ 
% 0.82/1.02           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 0.82/1.02           (u1_struct_0 @ sk_A))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.82/1.02      inference('sup-', [status(thm)], ['103', '111'])).
% 0.82/1.02  thf('113', plain,
% 0.82/1.02      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02          = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | (m1_subset_1 @ 
% 0.82/1.02           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 0.82/1.02           (u1_struct_0 @ sk_A))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.82/1.02      inference('simplify', [status(thm)], ['112'])).
% 0.82/1.02  thf('114', plain,
% 0.82/1.02      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.82/1.02         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.82/1.02          | ~ (r2_lattice3 @ X18 @ (k1_tarski @ X19) @ X17)
% 0.82/1.02          | (r1_orders_2 @ X18 @ X19 @ X17)
% 0.82/1.02          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.82/1.02          | ~ (l1_orders_2 @ X18))),
% 0.82/1.02      inference('cnf', [status(esa)], [t7_yellow_0])).
% 0.82/1.02  thf('115', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         (((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02          | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02          | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02              = (k1_yellow_0 @ sk_A @ 
% 0.82/1.02                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02          | ~ (l1_orders_2 @ sk_A)
% 0.82/1.02          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.02          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.82/1.02             (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02              (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 0.82/1.02          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ 
% 0.82/1.02               (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['113', '114'])).
% 0.82/1.02  thf('116', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('117', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         (((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02          | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02          | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02              = (k1_yellow_0 @ sk_A @ 
% 0.82/1.02                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.02          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.82/1.02             (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02              (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 0.82/1.02          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ 
% 0.82/1.02               (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A)))),
% 0.82/1.02      inference('demod', [status(thm)], ['115', '116'])).
% 0.82/1.02  thf('118', plain,
% 0.82/1.02      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 0.82/1.02        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['102', '117'])).
% 0.82/1.02  thf('119', plain,
% 0.82/1.02      ((~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.02        | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.82/1.02      inference('simplify', [status(thm)], ['118'])).
% 0.82/1.02  thf('120', plain,
% 0.82/1.02      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['91', '119'])).
% 0.82/1.02  thf('121', plain,
% 0.82/1.02      (((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02         (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02          (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.82/1.02      inference('simplify', [status(thm)], ['120'])).
% 0.82/1.02  thf('122', plain,
% 0.82/1.02      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.82/1.02         (~ (r2_lattice3 @ X13 @ X14 @ X15)
% 0.82/1.02          | ~ (r1_orders_2 @ X13 @ X15 @ (sk_D_1 @ X15 @ X14 @ X13))
% 0.82/1.02          | ((X15) = (k1_yellow_0 @ X13 @ X14))
% 0.82/1.02          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.82/1.02          | ~ (r1_yellow_0 @ X13 @ X14)
% 0.82/1.02          | ~ (l1_orders_2 @ X13))),
% 0.82/1.02      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.82/1.02  thf('123', plain,
% 0.82/1.02      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | ~ (l1_orders_2 @ sk_A)
% 0.82/1.02        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.02        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | ~ (r2_lattice3 @ sk_A @ 
% 0.82/1.02             (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.82/1.02             (sk_D @ sk_D_2 @ sk_B @ sk_A)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['121', '122'])).
% 0.82/1.02  thf('124', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('125', plain,
% 0.82/1.02      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.02        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | ~ (r2_lattice3 @ sk_A @ 
% 0.82/1.02             (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.82/1.02             (sk_D @ sk_D_2 @ sk_B @ sk_A)))),
% 0.82/1.02      inference('demod', [status(thm)], ['123', '124'])).
% 0.82/1.02  thf('126', plain,
% 0.82/1.02      ((~ (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.82/1.02           (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.82/1.02        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.02        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.82/1.02      inference('simplify', [status(thm)], ['125'])).
% 0.82/1.02  thf('127', plain,
% 0.82/1.02      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.02        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['90', '126'])).
% 0.82/1.02  thf('128', plain,
% 0.82/1.02      ((~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.02        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.82/1.02      inference('simplify', [status(thm)], ['127'])).
% 0.82/1.02  thf('129', plain,
% 0.82/1.02      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))),
% 0.82/1.02      inference('sup-', [status(thm)], ['73', '128'])).
% 0.82/1.02  thf('130', plain,
% 0.82/1.02      ((~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.82/1.02      inference('simplify', [status(thm)], ['129'])).
% 0.82/1.02  thf('131', plain,
% 0.82/1.02      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.82/1.02      inference('sup-', [status(thm)], ['72', '130'])).
% 0.82/1.02  thf('132', plain,
% 0.82/1.02      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.82/1.02          = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.82/1.02      inference('simplify', [status(thm)], ['131'])).
% 0.82/1.02  thf('133', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.82/1.02             (k1_zfmisc_1 @ X0)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['66', '67'])).
% 0.82/1.02  thf('134', plain,
% 0.82/1.02      (![X24 : $i]:
% 0.82/1.02         (((X24) = (k1_xboole_0))
% 0.82/1.02          | (r2_hidden @ (k1_yellow_0 @ sk_A @ X24) @ sk_C)
% 0.82/1.02          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ sk_B))
% 0.82/1.02          | ~ (v1_finset_1 @ X24))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('135', plain,
% 0.82/1.02      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.82/1.02        | (r2_hidden @ 
% 0.82/1.02           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.82/1.02           sk_C)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['133', '134'])).
% 0.82/1.02  thf('136', plain, (![X6 : $i]: (v1_finset_1 @ (k1_tarski @ X6))),
% 0.82/1.02      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.82/1.02  thf('137', plain,
% 0.82/1.02      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | (r2_hidden @ 
% 0.82/1.02           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.82/1.02           sk_C)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.82/1.02      inference('demod', [status(thm)], ['135', '136'])).
% 0.82/1.02  thf('138', plain,
% 0.82/1.02      (![X1 : $i, X2 : $i]:
% 0.82/1.02         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.82/1.02          | ~ (r2_hidden @ X1 @ X2))),
% 0.82/1.02      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.82/1.02  thf('139', plain,
% 0.82/1.02      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | (m1_subset_1 @ 
% 0.82/1.02           (k1_tarski @ 
% 0.82/1.02            (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 0.82/1.02           (k1_zfmisc_1 @ sk_C)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['137', '138'])).
% 0.82/1.02  thf('140', plain,
% 0.82/1.02      (![X3 : $i, X4 : $i]:
% 0.82/1.02         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.82/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.82/1.02  thf('141', plain,
% 0.82/1.02      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02        | (r1_tarski @ 
% 0.82/1.02           (k1_tarski @ 
% 0.82/1.02            (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 0.82/1.02           sk_C))),
% 0.82/1.02      inference('sup-', [status(thm)], ['139', '140'])).
% 0.82/1.02  thf('142', plain,
% 0.82/1.02      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.82/1.02         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.02      inference('split', [status(esa)], ['24'])).
% 0.82/1.02  thf('143', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]:
% 0.82/1.02         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.82/1.02          | ~ (r1_tarski @ X0 @ X1))),
% 0.82/1.02      inference('demod', [status(thm)], ['28', '29'])).
% 0.82/1.02  thf('144', plain,
% 0.82/1.02      ((![X0 : $i]:
% 0.82/1.02          (~ (r1_tarski @ X0 @ sk_C) | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 0.82/1.02         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['142', '143'])).
% 0.82/1.02  thf('145', plain,
% 0.82/1.02      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02         | (r2_lattice3 @ sk_A @ 
% 0.82/1.02            (k1_tarski @ 
% 0.82/1.02             (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 0.82/1.02            sk_D_2)))
% 0.82/1.02         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['141', '144'])).
% 0.82/1.02  thf('146', plain,
% 0.82/1.02      ((((r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.82/1.02          sk_D_2)
% 0.82/1.02         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.82/1.02         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.02      inference('sup+', [status(thm)], ['132', '145'])).
% 0.82/1.02  thf('147', plain,
% 0.82/1.02      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02         | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.82/1.02            sk_D_2)))
% 0.82/1.02         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.02      inference('simplify', [status(thm)], ['146'])).
% 0.82/1.02  thf('148', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('149', plain,
% 0.82/1.02      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.82/1.02         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.82/1.02          | ~ (r2_lattice3 @ X18 @ (k1_tarski @ X19) @ X17)
% 0.82/1.02          | (r1_orders_2 @ X18 @ X19 @ X17)
% 0.82/1.02          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.82/1.02          | ~ (l1_orders_2 @ X18))),
% 0.82/1.02      inference('cnf', [status(esa)], [t7_yellow_0])).
% 0.82/1.02  thf('150', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         (~ (l1_orders_2 @ sk_A)
% 0.82/1.02          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.02          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.82/1.02      inference('sup-', [status(thm)], ['148', '149'])).
% 0.82/1.02  thf('151', plain, ((l1_orders_2 @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('152', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.02          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.82/1.02      inference('demod', [status(thm)], ['150', '151'])).
% 0.82/1.02  thf('153', plain,
% 0.82/1.02      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.82/1.02         | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.82/1.02              (u1_struct_0 @ sk_A))))
% 0.82/1.02         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['147', '152'])).
% 0.82/1.02  thf('154', plain,
% 0.82/1.02      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.82/1.02         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.82/1.02         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['65', '153'])).
% 0.82/1.02  thf('155', plain,
% 0.82/1.02      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.82/1.02         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.82/1.02         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.82/1.02         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.02      inference('simplify', [status(thm)], ['154'])).
% 0.82/1.02  thf('156', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.82/1.02          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.82/1.02      inference('demod', [status(thm)], ['58', '59'])).
% 0.82/1.02  thf('157', plain,
% 0.82/1.02      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.82/1.02         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.82/1.02         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.02      inference('clc', [status(thm)], ['155', '156'])).
% 0.82/1.02  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.82/1.02  thf('158', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.82/1.02      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.82/1.02  thf('159', plain,
% 0.82/1.02      (((~ (v1_xboole_0 @ k1_xboole_0) | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.82/1.02         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['157', '158'])).
% 0.82/1.02  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.82/1.02  thf('160', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.82/1.02      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.82/1.02  thf('161', plain,
% 0.82/1.02      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.82/1.02         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.82/1.02      inference('demod', [status(thm)], ['159', '160'])).
% 0.82/1.02  thf('162', plain,
% 0.82/1.02      ((~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.82/1.02         <= (~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.82/1.02      inference('split', [status(esa)], ['0'])).
% 0.82/1.02  thf('163', plain,
% 0.82/1.02      (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.82/1.02       ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.82/1.02      inference('sup-', [status(thm)], ['161', '162'])).
% 0.82/1.02  thf('164', plain, ($false),
% 0.82/1.02      inference('sat_resolution*', [status(thm)], ['1', '63', '64', '163'])).
% 0.82/1.02  
% 0.82/1.02  % SZS output end Refutation
% 0.82/1.02  
% 0.82/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
