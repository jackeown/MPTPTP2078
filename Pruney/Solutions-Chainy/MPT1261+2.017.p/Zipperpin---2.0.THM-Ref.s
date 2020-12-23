%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9dg3QZEB84

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:39 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 226 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  855 (3064 expanded)
%              Number of equality atoms :   63 ( 182 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_tops_1 @ X30 @ X29 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k2_pre_topc @ X30 @ X29 ) @ ( k1_tops_1 @ X30 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k3_tarski @ ( k2_tarski @ X19 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X4 @ X3 ) )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('44',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_pre_topc @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
       != X25 )
      | ( v4_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('54',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('56',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','54','55'])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['12','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('59',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','57','58'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['14','54'])).

thf('64',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9dg3QZEB84
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 251 iterations in 0.105s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.56  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.56  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.36/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.36/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.56  thf(t77_tops_1, conjecture,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.56             ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.56               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i]:
% 0.36/0.56        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56          ( ![B:$i]:
% 0.36/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56              ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.56                ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.56                  ( k7_subset_1 @
% 0.36/0.56                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(l78_tops_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.56             ( k7_subset_1 @
% 0.36/0.56               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.36/0.56               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      (![X29 : $i, X30 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.36/0.56          | ((k2_tops_1 @ X30 @ X29)
% 0.36/0.56              = (k7_subset_1 @ (u1_struct_0 @ X30) @ 
% 0.36/0.56                 (k2_pre_topc @ X30 @ X29) @ (k1_tops_1 @ X30 @ X29)))
% 0.36/0.56          | ~ (l1_pre_topc @ X30))),
% 0.36/0.56      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.56               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.56  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.56            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56             (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.56        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['5'])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t52_pre_topc, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.36/0.56             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.36/0.56               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (![X25 : $i, X26 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.56          | ~ (v4_pre_topc @ X25 @ X26)
% 0.36/0.56          | ((k2_pre_topc @ X26 @ X25) = (X25))
% 0.36/0.56          | ~ (l1_pre_topc @ X26))),
% 0.36/0.56      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.36/0.56        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.36/0.56         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['6', '11'])).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56              (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.56        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (~
% 0.36/0.56       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.36/0.56       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.56      inference('split', [status(esa)], ['13'])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t65_tops_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ( k2_pre_topc @ A @ B ) =
% 0.36/0.56             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      (![X31 : $i, X32 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.36/0.56          | ((k2_pre_topc @ X32 @ X31)
% 0.36/0.56              = (k4_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.36/0.56                 (k2_tops_1 @ X32 @ X31)))
% 0.36/0.56          | ~ (l1_pre_topc @ X32))),
% 0.36/0.56      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.56            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.56  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(dt_k2_tops_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.56       ( m1_subset_1 @
% 0.36/0.56         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      (![X27 : $i, X28 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ X27)
% 0.36/0.56          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.36/0.56          | (m1_subset_1 @ (k2_tops_1 @ X27 @ X28) @ 
% 0.36/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 0.36/0.56      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.36/0.56  thf('21', plain,
% 0.36/0.56      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.56  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(redefinition_k4_subset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.36/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.56       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.36/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.36/0.56          | ((k4_subset_1 @ X20 @ X19 @ X21) = (k2_xboole_0 @ X19 @ X21)))),
% 0.36/0.56      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.36/0.56  thf(l51_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.56  thf('26', plain,
% 0.36/0.56      (![X17 : $i, X18 : $i]:
% 0.36/0.56         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.36/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.56  thf('27', plain,
% 0.36/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.36/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.36/0.56          | ((k4_subset_1 @ X20 @ X19 @ X21)
% 0.36/0.56              = (k3_tarski @ (k2_tarski @ X19 @ X21))))),
% 0.36/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.56            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['24', '27'])).
% 0.36/0.56  thf('29', plain,
% 0.36/0.56      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.56         = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['23', '28'])).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      (((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.56         = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.56      inference('demod', [status(thm)], ['17', '18', '29'])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(redefinition_k7_subset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.56       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.36/0.56          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.36/0.56      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.56           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.56  thf('34', plain,
% 0.36/0.56      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56             (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.56         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.56      inference('split', [status(esa)], ['5'])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.56         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.56      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.56  thf(t36_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.36/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.56  thf(t12_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i]:
% 0.36/0.56         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.36/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      (![X17 : $i, X18 : $i]:
% 0.36/0.56         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.36/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.56  thf('39', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i]:
% 0.36/0.56         (((k3_tarski @ (k2_tarski @ X4 @ X3)) = (X3))
% 0.36/0.56          | ~ (r1_tarski @ X4 @ X3))),
% 0.36/0.56      inference('demod', [status(thm)], ['37', '38'])).
% 0.36/0.56  thf('40', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((k3_tarski @ (k2_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)) = (X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['36', '39'])).
% 0.36/0.56  thf(commutativity_k2_tarski, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.36/0.56  thf('41', plain,
% 0.36/0.56      (![X15 : $i, X16 : $i]:
% 0.36/0.56         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.36/0.56      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((k3_tarski @ (k2_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))) = (X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.56  thf('43', plain,
% 0.36/0.56      ((((k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.36/0.56         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.56      inference('sup+', [status(thm)], ['35', '42'])).
% 0.36/0.56  thf('44', plain,
% 0.36/0.56      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.36/0.56         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.56      inference('sup+', [status(thm)], ['30', '43'])).
% 0.36/0.56  thf('45', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('46', plain,
% 0.36/0.56      (![X25 : $i, X26 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.56          | ~ (v2_pre_topc @ X26)
% 0.36/0.56          | ((k2_pre_topc @ X26 @ X25) != (X25))
% 0.36/0.56          | (v4_pre_topc @ X25 @ X26)
% 0.36/0.56          | ~ (l1_pre_topc @ X26))),
% 0.36/0.56      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | (v4_pre_topc @ sk_B @ sk_A)
% 0.36/0.56        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.36/0.56        | ~ (v2_pre_topc @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.56  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('50', plain,
% 0.36/0.56      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.36/0.56      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.36/0.56  thf('51', plain,
% 0.36/0.56      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.36/0.56         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['44', '50'])).
% 0.36/0.56  thf('52', plain,
% 0.36/0.56      (((v4_pre_topc @ sk_B @ sk_A))
% 0.36/0.56         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['51'])).
% 0.36/0.56  thf('53', plain,
% 0.36/0.56      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['13'])).
% 0.36/0.56  thf('54', plain,
% 0.36/0.56      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.36/0.56       ~
% 0.36/0.56       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.36/0.56       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.56      inference('split', [status(esa)], ['5'])).
% 0.36/0.56  thf('56', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['14', '54', '55'])).
% 0.36/0.56  thf('57', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['12', '56'])).
% 0.36/0.56  thf('58', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.56           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.56  thf('59', plain,
% 0.36/0.56      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('demod', [status(thm)], ['4', '57', '58'])).
% 0.36/0.56  thf('60', plain,
% 0.36/0.56      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56              (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.56         <= (~
% 0.36/0.56             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.56      inference('split', [status(esa)], ['13'])).
% 0.36/0.56  thf('61', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.56           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.56  thf('62', plain,
% 0.36/0.56      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.56         <= (~
% 0.36/0.56             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.56      inference('demod', [status(thm)], ['60', '61'])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      (~
% 0.36/0.56       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.56             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['14', '54'])).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.56         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.36/0.56  thf('65', plain, ($false),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['59', '64'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
