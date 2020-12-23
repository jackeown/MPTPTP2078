%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.otjvU5bIRr

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:07 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  206 (1889 expanded)
%              Number of leaves         :   41 ( 582 expanded)
%              Depth                    :   24
%              Number of atoms          : 1593 (25611 expanded)
%              Number of equality atoms :   37 ( 818 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(t13_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( ( v1_borsuk_1 @ C @ A )
                    & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ( ( C
                    = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                 => ( ( ( v1_borsuk_1 @ B @ A )
                      & ( m1_pre_topc @ B @ A ) )
                  <=> ( ( v1_borsuk_1 @ C @ A )
                      & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_tmap_1])).

thf('0',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t11_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( X36
       != ( u1_struct_0 @ X34 ) )
      | ~ ( v1_borsuk_1 @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( v4_pre_topc @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('13',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X34 ) @ X35 )
      | ~ ( v1_borsuk_1 @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('22',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X8: $i] :
      ( ( k1_subset_1 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = ( k3_subset_1 @ X12 @ ( k1_subset_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('26',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,(
    ! [X12: $i] :
      ( X12
      = ( k3_subset_1 @ X12 @ ( k1_subset_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('33',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_pre_topc @ X24 @ ( g1_pre_topc @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) ) ) ) )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('49',plain,(
    ! [X11: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('50',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('57',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('58',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v4_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v4_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v4_pre_topc @ X27 @ ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) ) ) )
      | ( v4_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,
    ( ~ ( v4_pre_topc @ k1_xboole_0 @ sk_C_1 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('71',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('75',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_pre_topc @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) ) ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X11: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('85',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('87',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ~ ( v1_borsuk_1 @ sk_B @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','88','89','90'])).

thf('92',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','91'])).

thf('93',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('96',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( X36
       != ( u1_struct_0 @ X34 ) )
      | ~ ( v4_pre_topc @ X36 @ X35 )
      | ( v1_borsuk_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('100',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v1_borsuk_1 @ X34 @ X35 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X34 ) @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ( v1_borsuk_1 @ sk_C_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','100'])).

thf('102',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['93'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ( v1_borsuk_1 @ sk_C_1 @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','105'])).

thf('107',plain,
    ( ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('110',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X32 ) @ ( u1_pre_topc @ X32 ) ) @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('111',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('116',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
   <= ( v1_borsuk_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('118',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('119',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X34 ) @ X35 )
      | ~ ( v1_borsuk_1 @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('120',plain,
    ( ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['93'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
      & ( m1_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','124'])).

thf('126',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('127',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v1_borsuk_1 @ X34 @ X35 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X34 ) @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('128',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_borsuk_1 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('130',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','87'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ( v1_borsuk_1 @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','133'])).

thf('135',plain,
    ( ~ ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('136',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','4','108','116','136'])).

thf('138',plain,(
    ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','137'])).

thf('139',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['93'])).

thf('140',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['140'])).

thf('142',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','4','108','116','136','141'])).

thf('143',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['139','142'])).

thf('144',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','87'])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('145',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( X37
       != ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( m1_pre_topc @ X38 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('146',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( m1_pre_topc @ X38 @ X39 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) @ X39 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','146'])).

thf('148',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','87'])).

thf('150',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','87'])).

thf('153',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('154',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','87'])).

thf('156',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('157',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['147','150','151','152','153','154','155','156','157','158'])).

thf('160',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['143','159'])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['138','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.otjvU5bIRr
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 515 iterations in 0.229s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.69  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.46/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.69  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.69  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.69  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.46/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.69  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.46/0.69  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.46/0.69  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.69  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.69  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.69  thf(t13_tmap_1, conjecture,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.46/0.69           ( ![C:$i]:
% 0.46/0.69             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.46/0.69               ( ( ( C ) =
% 0.46/0.69                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.46/0.69                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.46/0.69                   ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i]:
% 0.46/0.69        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.69          ( ![B:$i]:
% 0.46/0.69            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.46/0.69              ( ![C:$i]:
% 0.46/0.69                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.46/0.69                  ( ( ( C ) =
% 0.46/0.69                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.46/0.69                    ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.46/0.69                      ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t13_tmap_1])).
% 0.46/0.69  thf('0', plain,
% 0.46/0.69      ((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.46/0.69        | ~ (v1_borsuk_1 @ sk_C_1 @ sk_A)
% 0.46/0.69        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.69        | ~ (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('1', plain,
% 0.46/0.69      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['0'])).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      (((v1_borsuk_1 @ sk_C_1 @ sk_A) | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('3', plain,
% 0.46/0.69      (((v1_borsuk_1 @ sk_C_1 @ sk_A)) | ((v1_borsuk_1 @ sk_B @ sk_A))),
% 0.46/0.69      inference('split', [status(esa)], ['2'])).
% 0.46/0.69  thf('4', plain,
% 0.46/0.69      (~ ((m1_pre_topc @ sk_B @ sk_A)) | ~ ((v1_borsuk_1 @ sk_B @ sk_A)) | 
% 0.46/0.69       ~ ((m1_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v1_borsuk_1 @ sk_C_1 @ sk_A))),
% 0.46/0.69      inference('split', [status(esa)], ['0'])).
% 0.46/0.69  thf('5', plain,
% 0.46/0.69      (((v1_borsuk_1 @ sk_B @ sk_A)) <= (((v1_borsuk_1 @ sk_B @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['2'])).
% 0.46/0.69  thf('6', plain,
% 0.46/0.69      (((v1_borsuk_1 @ sk_C_1 @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('7', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['6'])).
% 0.46/0.69  thf(t1_tsep_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_pre_topc @ A ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.69           ( m1_subset_1 @
% 0.46/0.69             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.69  thf('8', plain,
% 0.46/0.69      (![X40 : $i, X41 : $i]:
% 0.46/0.69         (~ (m1_pre_topc @ X40 @ X41)
% 0.46/0.69          | (m1_subset_1 @ (u1_struct_0 @ X40) @ 
% 0.46/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.46/0.69          | ~ (l1_pre_topc @ X41))),
% 0.46/0.69      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.46/0.69  thf('9', plain,
% 0.46/0.69      (((~ (l1_pre_topc @ sk_A)
% 0.46/0.69         | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.69         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.69  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('11', plain,
% 0.46/0.69      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.69         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.69  thf(t11_tsep_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.69           ( ![C:$i]:
% 0.46/0.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.46/0.69                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.46/0.69                   ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.46/0.69  thf('12', plain,
% 0.46/0.69      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.69         (~ (m1_pre_topc @ X34 @ X35)
% 0.46/0.69          | ((X36) != (u1_struct_0 @ X34))
% 0.46/0.69          | ~ (v1_borsuk_1 @ X34 @ X35)
% 0.46/0.69          | ~ (m1_pre_topc @ X34 @ X35)
% 0.46/0.69          | (v4_pre_topc @ X36 @ X35)
% 0.46/0.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.46/0.69          | ~ (l1_pre_topc @ X35)
% 0.46/0.69          | ~ (v2_pre_topc @ X35))),
% 0.46/0.69      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.46/0.69  thf('13', plain,
% 0.46/0.69      (![X34 : $i, X35 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ X35)
% 0.46/0.69          | ~ (l1_pre_topc @ X35)
% 0.46/0.69          | ~ (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.46/0.69               (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.46/0.69          | (v4_pre_topc @ (u1_struct_0 @ X34) @ X35)
% 0.46/0.69          | ~ (v1_borsuk_1 @ X34 @ X35)
% 0.46/0.69          | ~ (m1_pre_topc @ X34 @ X35))),
% 0.46/0.69      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.69  thf('14', plain,
% 0.46/0.69      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.69         | ~ (v1_borsuk_1 @ sk_B @ sk_A)
% 0.46/0.69         | (v4_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.69         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['11', '13'])).
% 0.46/0.69  thf('15', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['6'])).
% 0.46/0.69  thf(t4_subset_1, axiom,
% 0.46/0.69    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.69  thf('16', plain,
% 0.46/0.69      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.69  thf(cc2_pre_topc, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      (![X19 : $i, X20 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.69          | (v4_pre_topc @ X19 @ X20)
% 0.46/0.69          | ~ (v1_xboole_0 @ X19)
% 0.46/0.69          | ~ (l1_pre_topc @ X20)
% 0.46/0.69          | ~ (v2_pre_topc @ X20))),
% 0.46/0.69      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.46/0.69  thf('18', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0)
% 0.46/0.69          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.69  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('20', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0)
% 0.46/0.69          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.69      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.69  thf('21', plain,
% 0.46/0.69      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.69  thf(t29_tops_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_pre_topc @ A ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69           ( ( v4_pre_topc @ B @ A ) <=>
% 0.46/0.69             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      (![X30 : $i, X31 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.69          | ~ (v4_pre_topc @ X30 @ X31)
% 0.46/0.69          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X31) @ X30) @ X31)
% 0.46/0.69          | ~ (l1_pre_topc @ X31))),
% 0.46/0.69      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.46/0.69  thf('23', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ X0)
% 0.46/0.69          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.46/0.69             X0)
% 0.46/0.69          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.69  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.69  thf('24', plain, (![X8 : $i]: ((k1_subset_1 @ X8) = (k1_xboole_0))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.46/0.69  thf(t22_subset_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.46/0.69  thf('25', plain,
% 0.46/0.69      (![X12 : $i]:
% 0.46/0.69         ((k2_subset_1 @ X12) = (k3_subset_1 @ X12 @ (k1_subset_1 @ X12)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.46/0.69  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.69  thf('26', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.46/0.69      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.69  thf('27', plain,
% 0.46/0.69      (![X12 : $i]: ((X12) = (k3_subset_1 @ X12 @ (k1_subset_1 @ X12)))),
% 0.46/0.69      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.69  thf('28', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['24', '27'])).
% 0.46/0.69  thf('29', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ X0)
% 0.46/0.69          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.69          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.69      inference('demod', [status(thm)], ['23', '28'])).
% 0.46/0.69  thf('30', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ X0)
% 0.46/0.69          | ~ (v2_pre_topc @ X0)
% 0.46/0.69          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['20', '29'])).
% 0.46/0.69  thf('31', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.69          | ~ (v2_pre_topc @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0))),
% 0.46/0.69      inference('simplify', [status(thm)], ['30'])).
% 0.46/0.69  thf(dt_k2_subset_1, axiom,
% 0.46/0.69    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.69  thf('32', plain,
% 0.46/0.69      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.46/0.69      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.46/0.69  thf('33', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.46/0.69      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.69  thf('34', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.46/0.69      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.69  thf('35', plain,
% 0.46/0.69      (((sk_C_1) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(t60_pre_topc, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.46/0.69             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.46/0.69           ( ( v3_pre_topc @
% 0.46/0.69               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.46/0.69             ( m1_subset_1 @
% 0.46/0.69               B @ 
% 0.46/0.69               ( k1_zfmisc_1 @
% 0.46/0.69                 ( u1_struct_0 @
% 0.46/0.69                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.69  thf('36', plain,
% 0.46/0.69      (![X24 : $i, X25 : $i]:
% 0.46/0.69         (~ (v3_pre_topc @ X24 @ 
% 0.46/0.69             (g1_pre_topc @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25)))
% 0.46/0.69          | ~ (m1_subset_1 @ X24 @ 
% 0.46/0.69               (k1_zfmisc_1 @ 
% 0.46/0.69                (u1_struct_0 @ 
% 0.46/0.69                 (g1_pre_topc @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25)))))
% 0.46/0.69          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.46/0.69          | ~ (l1_pre_topc @ X25)
% 0.46/0.69          | ~ (v2_pre_topc @ X25))),
% 0.46/0.69      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.46/0.69  thf('37', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.46/0.69          | ~ (v2_pre_topc @ sk_B)
% 0.46/0.69          | ~ (l1_pre_topc @ sk_B)
% 0.46/0.69          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.69          | ~ (v3_pre_topc @ X0 @ 
% 0.46/0.69               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.69  thf('38', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('40', plain,
% 0.46/0.69      (((sk_C_1) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('41', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.46/0.69          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.69          | ~ (v3_pre_topc @ X0 @ sk_C_1))),
% 0.46/0.69      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.46/0.69  thf('42', plain,
% 0.46/0.69      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_C_1)
% 0.46/0.69        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['34', '41'])).
% 0.46/0.69  thf('43', plain,
% 0.46/0.69      ((~ (l1_pre_topc @ sk_C_1)
% 0.46/0.69        | ~ (v2_pre_topc @ sk_C_1)
% 0.46/0.69        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['31', '42'])).
% 0.46/0.69  thf('44', plain, ((l1_pre_topc @ sk_C_1)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('45', plain, ((v2_pre_topc @ sk_C_1)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('46', plain,
% 0.46/0.69      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.69      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.46/0.69  thf(t2_subset, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.69       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.69  thf('47', plain,
% 0.46/0.69      (![X14 : $i, X15 : $i]:
% 0.46/0.69         ((r2_hidden @ X14 @ X15)
% 0.46/0.69          | (v1_xboole_0 @ X15)
% 0.46/0.69          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.46/0.69      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.69  thf('48', plain,
% 0.46/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.69        | (r2_hidden @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.69  thf(fc1_subset_1, axiom,
% 0.46/0.69    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.69  thf('49', plain, (![X11 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.69  thf('50', plain,
% 0.46/0.69      ((r2_hidden @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.69      inference('clc', [status(thm)], ['48', '49'])).
% 0.46/0.69  thf(d1_zfmisc_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.69  thf('51', plain,
% 0.46/0.69      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X6 @ X5)
% 0.46/0.69          | (r1_tarski @ X6 @ X4)
% 0.46/0.69          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.69  thf('52', plain,
% 0.46/0.69      (![X4 : $i, X6 : $i]:
% 0.46/0.69         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.69  thf('53', plain,
% 0.46/0.69      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['50', '52'])).
% 0.46/0.69  thf(d10_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.69  thf('54', plain,
% 0.46/0.69      (![X0 : $i, X2 : $i]:
% 0.46/0.69         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.69  thf('55', plain,
% 0.46/0.69      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.46/0.69        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.69  thf('56', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0)
% 0.46/0.69          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.69      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.69  thf('57', plain,
% 0.46/0.69      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.69  thf('58', plain,
% 0.46/0.69      (((sk_C_1) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(t61_pre_topc, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( ( v4_pre_topc @ B @ A ) & 
% 0.46/0.69             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.46/0.69           ( ( v4_pre_topc @
% 0.46/0.69               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.46/0.69             ( m1_subset_1 @
% 0.46/0.69               B @ 
% 0.46/0.69               ( k1_zfmisc_1 @
% 0.46/0.69                 ( u1_struct_0 @
% 0.46/0.69                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.69  thf('59', plain,
% 0.46/0.69      (![X27 : $i, X28 : $i]:
% 0.46/0.69         (~ (v4_pre_topc @ X27 @ 
% 0.46/0.69             (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28)))
% 0.46/0.69          | ~ (m1_subset_1 @ X27 @ 
% 0.46/0.69               (k1_zfmisc_1 @ 
% 0.46/0.69                (u1_struct_0 @ 
% 0.46/0.69                 (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28)))))
% 0.46/0.69          | (v4_pre_topc @ X27 @ X28)
% 0.46/0.69          | ~ (l1_pre_topc @ X28)
% 0.46/0.69          | ~ (v2_pre_topc @ X28))),
% 0.46/0.69      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.46/0.69  thf('60', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.46/0.69          | ~ (v2_pre_topc @ sk_B)
% 0.46/0.69          | ~ (l1_pre_topc @ sk_B)
% 0.46/0.69          | (v4_pre_topc @ X0 @ sk_B)
% 0.46/0.69          | ~ (v4_pre_topc @ X0 @ 
% 0.46/0.69               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.69  thf('61', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('63', plain,
% 0.46/0.69      (((sk_C_1) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('64', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.46/0.69          | (v4_pre_topc @ X0 @ sk_B)
% 0.46/0.69          | ~ (v4_pre_topc @ X0 @ sk_C_1))),
% 0.46/0.69      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.46/0.69  thf('65', plain,
% 0.46/0.69      ((~ (v4_pre_topc @ k1_xboole_0 @ sk_C_1)
% 0.46/0.69        | (v4_pre_topc @ k1_xboole_0 @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['57', '64'])).
% 0.46/0.69  thf('66', plain,
% 0.46/0.69      ((~ (l1_pre_topc @ sk_C_1)
% 0.46/0.69        | ~ (v2_pre_topc @ sk_C_1)
% 0.46/0.69        | (v4_pre_topc @ k1_xboole_0 @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['56', '65'])).
% 0.46/0.69  thf('67', plain, ((l1_pre_topc @ sk_C_1)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('68', plain, ((v2_pre_topc @ sk_C_1)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('69', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_B)),
% 0.46/0.69      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.46/0.69  thf('70', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ X0)
% 0.46/0.69          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.69          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.69      inference('demod', [status(thm)], ['23', '28'])).
% 0.46/0.69  thf('71', plain,
% 0.46/0.69      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_B) | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.69  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('73', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_B)),
% 0.46/0.69      inference('demod', [status(thm)], ['71', '72'])).
% 0.46/0.69  thf('74', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.46/0.69      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.69  thf('75', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i]:
% 0.46/0.69         (~ (v3_pre_topc @ X26 @ X25)
% 0.46/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.46/0.69          | (m1_subset_1 @ X26 @ 
% 0.46/0.69             (k1_zfmisc_1 @ 
% 0.46/0.69              (u1_struct_0 @ 
% 0.46/0.69               (g1_pre_topc @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25)))))
% 0.46/0.69          | ~ (l1_pre_topc @ X25)
% 0.46/0.69          | ~ (v2_pre_topc @ X25))),
% 0.46/0.69      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.46/0.69  thf('76', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0)
% 0.46/0.69          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.46/0.69             (k1_zfmisc_1 @ 
% 0.46/0.69              (u1_struct_0 @ 
% 0.46/0.69               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.46/0.69          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['74', '75'])).
% 0.46/0.69  thf('77', plain,
% 0.46/0.69      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69         (k1_zfmisc_1 @ 
% 0.46/0.69          (u1_struct_0 @ 
% 0.46/0.69           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.46/0.69        | ~ (l1_pre_topc @ sk_B)
% 0.46/0.69        | ~ (v2_pre_topc @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['73', '76'])).
% 0.46/0.69  thf('78', plain,
% 0.46/0.69      (((sk_C_1) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('80', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('81', plain,
% 0.46/0.69      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.46/0.69      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.46/0.69  thf('82', plain,
% 0.46/0.69      (![X14 : $i, X15 : $i]:
% 0.46/0.69         ((r2_hidden @ X14 @ X15)
% 0.46/0.69          | (v1_xboole_0 @ X15)
% 0.46/0.69          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.46/0.69      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.69  thf('83', plain,
% 0.46/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.46/0.69        | (r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.69  thf('84', plain, (![X11 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.69  thf('85', plain,
% 0.46/0.69      ((r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.46/0.69      inference('clc', [status(thm)], ['83', '84'])).
% 0.46/0.69  thf('86', plain,
% 0.46/0.69      (![X4 : $i, X6 : $i]:
% 0.46/0.69         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.69  thf('87', plain,
% 0.46/0.69      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['85', '86'])).
% 0.46/0.69  thf('88', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.46/0.69      inference('demod', [status(thm)], ['55', '87'])).
% 0.46/0.69  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('91', plain,
% 0.46/0.69      (((~ (v1_borsuk_1 @ sk_B @ sk_A)
% 0.46/0.69         | (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)))
% 0.46/0.69         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['14', '15', '88', '89', '90'])).
% 0.46/0.69  thf('92', plain,
% 0.46/0.69      (((v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A))
% 0.46/0.69         <= (((v1_borsuk_1 @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['5', '91'])).
% 0.46/0.69  thf('93', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_C_1 @ sk_A) | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('94', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['93'])).
% 0.46/0.69  thf('95', plain,
% 0.46/0.69      (![X40 : $i, X41 : $i]:
% 0.46/0.69         (~ (m1_pre_topc @ X40 @ X41)
% 0.46/0.69          | (m1_subset_1 @ (u1_struct_0 @ X40) @ 
% 0.46/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.46/0.69          | ~ (l1_pre_topc @ X41))),
% 0.46/0.69      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.46/0.69  thf('96', plain,
% 0.46/0.69      (((~ (l1_pre_topc @ sk_A)
% 0.46/0.69         | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.69            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.69         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['94', '95'])).
% 0.46/0.69  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('98', plain,
% 0.46/0.69      (((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.69         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['96', '97'])).
% 0.46/0.69  thf('99', plain,
% 0.46/0.69      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.69         (~ (m1_pre_topc @ X34 @ X35)
% 0.46/0.69          | ((X36) != (u1_struct_0 @ X34))
% 0.46/0.69          | ~ (v4_pre_topc @ X36 @ X35)
% 0.46/0.69          | (v1_borsuk_1 @ X34 @ X35)
% 0.46/0.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.46/0.69          | ~ (l1_pre_topc @ X35)
% 0.46/0.69          | ~ (v2_pre_topc @ X35))),
% 0.46/0.69      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.46/0.69  thf('100', plain,
% 0.46/0.69      (![X34 : $i, X35 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ X35)
% 0.46/0.69          | ~ (l1_pre_topc @ X35)
% 0.46/0.69          | ~ (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.46/0.69               (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.46/0.69          | (v1_borsuk_1 @ X34 @ X35)
% 0.46/0.69          | ~ (v4_pre_topc @ (u1_struct_0 @ X34) @ X35)
% 0.46/0.69          | ~ (m1_pre_topc @ X34 @ X35))),
% 0.46/0.69      inference('simplify', [status(thm)], ['99'])).
% 0.46/0.69  thf('101', plain,
% 0.46/0.69      (((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.46/0.69         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.46/0.69         | (v1_borsuk_1 @ sk_C_1 @ sk_A)
% 0.46/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.69         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['98', '100'])).
% 0.46/0.69  thf('102', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['93'])).
% 0.46/0.69  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('105', plain,
% 0.46/0.69      (((~ (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.46/0.69         | (v1_borsuk_1 @ sk_C_1 @ sk_A))) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.46/0.69  thf('106', plain,
% 0.46/0.69      (((v1_borsuk_1 @ sk_C_1 @ sk_A))
% 0.46/0.69         <= (((v1_borsuk_1 @ sk_B @ sk_A)) & 
% 0.46/0.69             ((m1_pre_topc @ sk_B @ sk_A)) & 
% 0.46/0.69             ((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['92', '105'])).
% 0.46/0.69  thf('107', plain,
% 0.46/0.69      ((~ (v1_borsuk_1 @ sk_C_1 @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['0'])).
% 0.46/0.69  thf('108', plain,
% 0.46/0.69      (((v1_borsuk_1 @ sk_C_1 @ sk_A)) | ~ ((v1_borsuk_1 @ sk_B @ sk_A)) | 
% 0.46/0.69       ~ ((m1_pre_topc @ sk_C_1 @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['106', '107'])).
% 0.46/0.69  thf('109', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['6'])).
% 0.46/0.69  thf(t11_tmap_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_pre_topc @ A ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.69           ( ( v1_pre_topc @
% 0.46/0.69               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.46/0.69             ( m1_pre_topc @
% 0.46/0.69               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.46/0.69  thf('110', plain,
% 0.46/0.69      (![X32 : $i, X33 : $i]:
% 0.46/0.69         (~ (m1_pre_topc @ X32 @ X33)
% 0.46/0.69          | (m1_pre_topc @ 
% 0.46/0.69             (g1_pre_topc @ (u1_struct_0 @ X32) @ (u1_pre_topc @ X32)) @ X33)
% 0.46/0.69          | ~ (l1_pre_topc @ X33))),
% 0.46/0.69      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.46/0.69  thf('111', plain,
% 0.46/0.69      (((~ (l1_pre_topc @ sk_A)
% 0.46/0.69         | (m1_pre_topc @ 
% 0.46/0.69            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)))
% 0.46/0.69         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['109', '110'])).
% 0.46/0.69  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('113', plain,
% 0.46/0.69      (((sk_C_1) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('114', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.46/0.69  thf('115', plain,
% 0.46/0.69      ((~ (m1_pre_topc @ sk_C_1 @ sk_A)) <= (~ ((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['0'])).
% 0.46/0.69  thf('116', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_C_1 @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['114', '115'])).
% 0.46/0.69  thf('117', plain,
% 0.46/0.69      (((v1_borsuk_1 @ sk_C_1 @ sk_A)) <= (((v1_borsuk_1 @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['2'])).
% 0.46/0.69  thf('118', plain,
% 0.46/0.69      (((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.69         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['96', '97'])).
% 0.46/0.69  thf('119', plain,
% 0.46/0.69      (![X34 : $i, X35 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ X35)
% 0.46/0.69          | ~ (l1_pre_topc @ X35)
% 0.46/0.69          | ~ (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.46/0.69               (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.46/0.69          | (v4_pre_topc @ (u1_struct_0 @ X34) @ X35)
% 0.46/0.69          | ~ (v1_borsuk_1 @ X34 @ X35)
% 0.46/0.69          | ~ (m1_pre_topc @ X34 @ X35))),
% 0.46/0.69      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.69  thf('120', plain,
% 0.46/0.69      (((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.46/0.69         | ~ (v1_borsuk_1 @ sk_C_1 @ sk_A)
% 0.46/0.69         | (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.46/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.69         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['118', '119'])).
% 0.46/0.69  thf('121', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['93'])).
% 0.46/0.69  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('124', plain,
% 0.46/0.69      (((~ (v1_borsuk_1 @ sk_C_1 @ sk_A)
% 0.46/0.69         | (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)))
% 0.46/0.69         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.46/0.69  thf('125', plain,
% 0.46/0.69      (((v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A))
% 0.46/0.69         <= (((v1_borsuk_1 @ sk_C_1 @ sk_A)) & ((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['117', '124'])).
% 0.46/0.69  thf('126', plain,
% 0.46/0.69      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.69         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.69  thf('127', plain,
% 0.46/0.69      (![X34 : $i, X35 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ X35)
% 0.46/0.69          | ~ (l1_pre_topc @ X35)
% 0.46/0.69          | ~ (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.46/0.69               (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.46/0.69          | (v1_borsuk_1 @ X34 @ X35)
% 0.46/0.69          | ~ (v4_pre_topc @ (u1_struct_0 @ X34) @ X35)
% 0.46/0.69          | ~ (m1_pre_topc @ X34 @ X35))),
% 0.46/0.69      inference('simplify', [status(thm)], ['99'])).
% 0.46/0.69  thf('128', plain,
% 0.46/0.69      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.69         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.69         | (v1_borsuk_1 @ sk_B @ sk_A)
% 0.46/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.69         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['126', '127'])).
% 0.46/0.69  thf('129', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['6'])).
% 0.46/0.69  thf('130', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.46/0.69      inference('demod', [status(thm)], ['55', '87'])).
% 0.46/0.69  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('132', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('133', plain,
% 0.46/0.69      (((~ (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.46/0.69         | (v1_borsuk_1 @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 0.46/0.69  thf('134', plain,
% 0.46/0.69      (((v1_borsuk_1 @ sk_B @ sk_A))
% 0.46/0.69         <= (((v1_borsuk_1 @ sk_C_1 @ sk_A)) & 
% 0.46/0.69             ((m1_pre_topc @ sk_B @ sk_A)) & 
% 0.46/0.69             ((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['125', '133'])).
% 0.46/0.69  thf('135', plain,
% 0.46/0.69      ((~ (v1_borsuk_1 @ sk_B @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_B @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['0'])).
% 0.46/0.69  thf('136', plain,
% 0.46/0.69      (((v1_borsuk_1 @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A)) | 
% 0.46/0.69       ~ ((m1_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v1_borsuk_1 @ sk_C_1 @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['134', '135'])).
% 0.46/0.69  thf('137', plain, (~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.46/0.69      inference('sat_resolution*', [status(thm)],
% 0.46/0.69                ['3', '4', '108', '116', '136'])).
% 0.46/0.69  thf('138', plain, (~ (m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.69      inference('simpl_trail', [status(thm)], ['1', '137'])).
% 0.46/0.69  thf('139', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['93'])).
% 0.46/0.69  thf('140', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_C_1 @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('141', plain,
% 0.46/0.69      (((m1_pre_topc @ sk_C_1 @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.46/0.69      inference('split', [status(esa)], ['140'])).
% 0.46/0.69  thf('142', plain, (((m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.46/0.69      inference('sat_resolution*', [status(thm)],
% 0.46/0.69                ['3', '4', '108', '116', '136', '141'])).
% 0.46/0.69  thf('143', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.46/0.69      inference('simpl_trail', [status(thm)], ['139', '142'])).
% 0.46/0.69  thf('144', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.46/0.69      inference('demod', [status(thm)], ['55', '87'])).
% 0.46/0.69  thf(t12_tmap_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_pre_topc @ A ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.46/0.69           ( ![C:$i]:
% 0.46/0.69             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.46/0.69               ( ( ( B ) =
% 0.46/0.69                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.46/0.69                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.46/0.69  thf('145', plain,
% 0.46/0.69      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ X37)
% 0.46/0.69          | ~ (l1_pre_topc @ X37)
% 0.46/0.69          | ((X37) != (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 0.46/0.69          | ~ (m1_pre_topc @ X37 @ X39)
% 0.46/0.69          | (m1_pre_topc @ X38 @ X39)
% 0.46/0.69          | ~ (l1_pre_topc @ X38)
% 0.46/0.69          | ~ (v2_pre_topc @ X38)
% 0.46/0.69          | ~ (l1_pre_topc @ X39))),
% 0.46/0.69      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.46/0.69  thf('146', plain,
% 0.46/0.69      (![X38 : $i, X39 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ X39)
% 0.46/0.69          | ~ (v2_pre_topc @ X38)
% 0.46/0.69          | ~ (l1_pre_topc @ X38)
% 0.46/0.69          | (m1_pre_topc @ X38 @ X39)
% 0.46/0.69          | ~ (m1_pre_topc @ 
% 0.46/0.69               (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)) @ X39)
% 0.46/0.69          | ~ (l1_pre_topc @ 
% 0.46/0.69               (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 0.46/0.69          | ~ (v2_pre_topc @ 
% 0.46/0.69               (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38))))),
% 0.46/0.69      inference('simplify', [status(thm)], ['145'])).
% 0.46/0.69  thf('147', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ 
% 0.46/0.69             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B)))
% 0.46/0.69          | ~ (v2_pre_topc @ 
% 0.46/0.69               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.69          | ~ (m1_pre_topc @ 
% 0.46/0.69               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.46/0.69          | (m1_pre_topc @ sk_B @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ sk_B)
% 0.46/0.69          | ~ (v2_pre_topc @ sk_B)
% 0.46/0.69          | ~ (l1_pre_topc @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['144', '146'])).
% 0.46/0.69  thf('148', plain,
% 0.46/0.69      (((sk_C_1) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('149', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.46/0.69      inference('demod', [status(thm)], ['55', '87'])).
% 0.46/0.69  thf('150', plain,
% 0.46/0.69      (((sk_C_1)
% 0.46/0.69         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.69      inference('demod', [status(thm)], ['148', '149'])).
% 0.46/0.69  thf('151', plain, ((l1_pre_topc @ sk_C_1)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('152', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.46/0.69      inference('demod', [status(thm)], ['55', '87'])).
% 0.46/0.69  thf('153', plain,
% 0.46/0.69      (((sk_C_1)
% 0.46/0.69         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.69      inference('demod', [status(thm)], ['148', '149'])).
% 0.46/0.69  thf('154', plain, ((v2_pre_topc @ sk_C_1)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('155', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.46/0.69      inference('demod', [status(thm)], ['55', '87'])).
% 0.46/0.69  thf('156', plain,
% 0.46/0.69      (((sk_C_1)
% 0.46/0.69         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.69      inference('demod', [status(thm)], ['148', '149'])).
% 0.46/0.69  thf('157', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('158', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('159', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.46/0.69          | (m1_pre_topc @ sk_B @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0))),
% 0.46/0.69      inference('demod', [status(thm)],
% 0.46/0.69                ['147', '150', '151', '152', '153', '154', '155', '156', 
% 0.46/0.69                 '157', '158'])).
% 0.46/0.69  thf('160', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['143', '159'])).
% 0.46/0.69  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('162', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['160', '161'])).
% 0.46/0.69  thf('163', plain, ($false), inference('demod', [status(thm)], ['138', '162'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.46/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
