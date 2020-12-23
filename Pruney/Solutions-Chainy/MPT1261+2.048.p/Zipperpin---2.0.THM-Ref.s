%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zBYfyLEkcc

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:44 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 238 expanded)
%              Number of leaves         :   41 (  85 expanded)
%              Depth                    :   17
%              Number of atoms          : 1305 (2694 expanded)
%              Number of equality atoms :  101 ( 191 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v4_pre_topc @ X44 @ X45 )
      | ( ( k2_pre_topc @ X45 @ X44 )
        = X44 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k2_tops_1 @ X49 @ X48 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X49 ) @ ( k2_pre_topc @ X49 @ X48 ) @ ( k1_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k4_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X26 @ X25 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k4_subset_1 @ X34 @ X33 @ X35 )
        = ( k2_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('42',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('64',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('66',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('68',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('76',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['74','76'])).

thf('78',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','77'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('79',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('80',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','56'])).

thf('82',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('85',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k2_pre_topc @ X53 @ X52 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X53 ) @ X52 @ ( k2_tops_1 @ X53 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['83','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('91',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X46 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('92',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['89','95'])).

thf('97',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zBYfyLEkcc
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.20/1.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.20/1.43  % Solved by: fo/fo7.sh
% 1.20/1.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.43  % done 2262 iterations in 0.973s
% 1.20/1.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.20/1.43  % SZS output start Refutation
% 1.20/1.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.20/1.43  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.20/1.43  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.20/1.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.43  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.20/1.43  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.20/1.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.20/1.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.20/1.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.20/1.43  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.20/1.43  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.20/1.43  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.20/1.43  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.20/1.43  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.20/1.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.20/1.43  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.20/1.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.20/1.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.43  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.20/1.43  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.20/1.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.20/1.43  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.43  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.43  thf(t77_tops_1, conjecture,
% 1.20/1.43    (![A:$i]:
% 1.20/1.43     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.20/1.43       ( ![B:$i]:
% 1.20/1.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.43           ( ( v4_pre_topc @ B @ A ) <=>
% 1.20/1.43             ( ( k2_tops_1 @ A @ B ) =
% 1.20/1.43               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.20/1.43  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.43    (~( ![A:$i]:
% 1.20/1.43        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.20/1.43          ( ![B:$i]:
% 1.20/1.43            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.43              ( ( v4_pre_topc @ B @ A ) <=>
% 1.20/1.43                ( ( k2_tops_1 @ A @ B ) =
% 1.20/1.43                  ( k7_subset_1 @
% 1.20/1.43                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.20/1.43    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.20/1.43  thf('0', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43              (k1_tops_1 @ sk_A @ sk_B)))
% 1.20/1.43        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf('1', plain,
% 1.20/1.43      (~
% 1.20/1.43       (((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.20/1.43       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.20/1.43      inference('split', [status(esa)], ['0'])).
% 1.20/1.43  thf('2', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43             (k1_tops_1 @ sk_A @ sk_B)))
% 1.20/1.43        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf('3', plain,
% 1.20/1.43      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.20/1.43      inference('split', [status(esa)], ['2'])).
% 1.20/1.43  thf('4', plain,
% 1.20/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf(t52_pre_topc, axiom,
% 1.20/1.43    (![A:$i]:
% 1.20/1.43     ( ( l1_pre_topc @ A ) =>
% 1.20/1.43       ( ![B:$i]:
% 1.20/1.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.43           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.20/1.43             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.20/1.43               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.20/1.43  thf('5', plain,
% 1.20/1.43      (![X44 : $i, X45 : $i]:
% 1.20/1.43         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.20/1.43          | ~ (v4_pre_topc @ X44 @ X45)
% 1.20/1.43          | ((k2_pre_topc @ X45 @ X44) = (X44))
% 1.20/1.43          | ~ (l1_pre_topc @ X45))),
% 1.20/1.43      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.20/1.43  thf('6', plain,
% 1.20/1.43      ((~ (l1_pre_topc @ sk_A)
% 1.20/1.43        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.20/1.43        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.20/1.43      inference('sup-', [status(thm)], ['4', '5'])).
% 1.20/1.43  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf('8', plain,
% 1.20/1.43      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.20/1.43      inference('demod', [status(thm)], ['6', '7'])).
% 1.20/1.43  thf('9', plain,
% 1.20/1.43      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.20/1.43         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.20/1.43      inference('sup-', [status(thm)], ['3', '8'])).
% 1.20/1.43  thf('10', plain,
% 1.20/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf(l78_tops_1, axiom,
% 1.20/1.43    (![A:$i]:
% 1.20/1.43     ( ( l1_pre_topc @ A ) =>
% 1.20/1.43       ( ![B:$i]:
% 1.20/1.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.43           ( ( k2_tops_1 @ A @ B ) =
% 1.20/1.43             ( k7_subset_1 @
% 1.20/1.43               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.20/1.43               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.20/1.43  thf('11', plain,
% 1.20/1.43      (![X48 : $i, X49 : $i]:
% 1.20/1.43         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 1.20/1.43          | ((k2_tops_1 @ X49 @ X48)
% 1.20/1.43              = (k7_subset_1 @ (u1_struct_0 @ X49) @ 
% 1.20/1.43                 (k2_pre_topc @ X49 @ X48) @ (k1_tops_1 @ X49 @ X48)))
% 1.20/1.43          | ~ (l1_pre_topc @ X49))),
% 1.20/1.43      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.20/1.43  thf('12', plain,
% 1.20/1.43      ((~ (l1_pre_topc @ sk_A)
% 1.20/1.43        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.43               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.20/1.43      inference('sup-', [status(thm)], ['10', '11'])).
% 1.20/1.43  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf('14', plain,
% 1.20/1.43      (((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.20/1.43            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.20/1.43      inference('demod', [status(thm)], ['12', '13'])).
% 1.20/1.43  thf('15', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43             (k1_tops_1 @ sk_A @ sk_B))))
% 1.20/1.43         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.20/1.43      inference('sup+', [status(thm)], ['9', '14'])).
% 1.20/1.43  thf('16', plain,
% 1.20/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf(redefinition_k7_subset_1, axiom,
% 1.20/1.43    (![A:$i,B:$i,C:$i]:
% 1.20/1.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.20/1.43       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.20/1.43  thf('17', plain,
% 1.20/1.43      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.20/1.43         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.20/1.43          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k4_xboole_0 @ X36 @ X38)))),
% 1.20/1.43      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.20/1.43  thf('18', plain,
% 1.20/1.43      (![X0 : $i]:
% 1.20/1.43         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.20/1.43           = (k4_xboole_0 @ sk_B @ X0))),
% 1.20/1.43      inference('sup-', [status(thm)], ['16', '17'])).
% 1.20/1.43  thf('19', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.20/1.43         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.20/1.43      inference('demod', [status(thm)], ['15', '18'])).
% 1.20/1.43  thf('20', plain,
% 1.20/1.43      (![X0 : $i]:
% 1.20/1.43         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.20/1.43           = (k4_xboole_0 @ sk_B @ X0))),
% 1.20/1.43      inference('sup-', [status(thm)], ['16', '17'])).
% 1.20/1.43  thf('21', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43              (k1_tops_1 @ sk_A @ sk_B))))
% 1.20/1.43         <= (~
% 1.20/1.43             (((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('split', [status(esa)], ['0'])).
% 1.20/1.43  thf('22', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.20/1.43         <= (~
% 1.20/1.43             (((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('sup-', [status(thm)], ['20', '21'])).
% 1.20/1.43  thf('23', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.20/1.43         <= (~
% 1.20/1.43             (((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.20/1.43             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.20/1.43      inference('sup-', [status(thm)], ['19', '22'])).
% 1.20/1.43  thf('24', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.20/1.43       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.20/1.43      inference('simplify', [status(thm)], ['23'])).
% 1.20/1.43  thf('25', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.20/1.43       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.20/1.43      inference('split', [status(esa)], ['2'])).
% 1.20/1.43  thf('26', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43             (k1_tops_1 @ sk_A @ sk_B))))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('split', [status(esa)], ['2'])).
% 1.20/1.43  thf('27', plain,
% 1.20/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf(dt_k7_subset_1, axiom,
% 1.20/1.43    (![A:$i,B:$i,C:$i]:
% 1.20/1.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.20/1.43       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.20/1.43  thf('28', plain,
% 1.20/1.43      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.20/1.43         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 1.20/1.43          | (m1_subset_1 @ (k7_subset_1 @ X26 @ X25 @ X27) @ 
% 1.20/1.43             (k1_zfmisc_1 @ X26)))),
% 1.20/1.43      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.20/1.43  thf('29', plain,
% 1.20/1.43      (![X0 : $i]:
% 1.20/1.43         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.20/1.43          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.43      inference('sup-', [status(thm)], ['27', '28'])).
% 1.20/1.43  thf('30', plain,
% 1.20/1.43      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.43         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('sup+', [status(thm)], ['26', '29'])).
% 1.20/1.43  thf('31', plain,
% 1.20/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf(redefinition_k4_subset_1, axiom,
% 1.20/1.43    (![A:$i,B:$i,C:$i]:
% 1.20/1.43     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.20/1.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.20/1.43       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.20/1.43  thf('32', plain,
% 1.20/1.43      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.20/1.43         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 1.20/1.43          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34))
% 1.20/1.43          | ((k4_subset_1 @ X34 @ X33 @ X35) = (k2_xboole_0 @ X33 @ X35)))),
% 1.20/1.43      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.20/1.43  thf('33', plain,
% 1.20/1.43      (![X0 : $i]:
% 1.20/1.43         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.20/1.43            = (k2_xboole_0 @ sk_B @ X0))
% 1.20/1.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.20/1.43      inference('sup-', [status(thm)], ['31', '32'])).
% 1.20/1.43  thf('34', plain,
% 1.20/1.43      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.20/1.43          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('sup-', [status(thm)], ['30', '33'])).
% 1.20/1.43  thf(d5_xboole_0, axiom,
% 1.20/1.43    (![A:$i,B:$i,C:$i]:
% 1.20/1.43     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.20/1.43       ( ![D:$i]:
% 1.20/1.43         ( ( r2_hidden @ D @ C ) <=>
% 1.20/1.43           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.20/1.43  thf('35', plain,
% 1.20/1.43      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.20/1.43         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.20/1.43          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.20/1.43          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.20/1.43      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.20/1.43  thf(t3_boole, axiom,
% 1.20/1.43    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.20/1.43  thf('36', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.20/1.43      inference('cnf', [status(esa)], [t3_boole])).
% 1.20/1.43  thf('37', plain,
% 1.20/1.43      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.20/1.43         (~ (r2_hidden @ X4 @ X3)
% 1.20/1.43          | ~ (r2_hidden @ X4 @ X2)
% 1.20/1.43          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.20/1.43      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.20/1.43  thf('38', plain,
% 1.20/1.43      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.20/1.43         (~ (r2_hidden @ X4 @ X2)
% 1.20/1.43          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.20/1.43      inference('simplify', [status(thm)], ['37'])).
% 1.20/1.43  thf('39', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]:
% 1.20/1.43         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.20/1.43      inference('sup-', [status(thm)], ['36', '38'])).
% 1.20/1.43  thf('40', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.20/1.43      inference('condensation', [status(thm)], ['39'])).
% 1.20/1.43  thf('41', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]:
% 1.20/1.43         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.20/1.43          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.20/1.43      inference('sup-', [status(thm)], ['35', '40'])).
% 1.20/1.43  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.20/1.43  thf('42', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 1.20/1.43      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.20/1.43  thf(t28_xboole_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]:
% 1.20/1.43     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.20/1.43  thf('43', plain,
% 1.20/1.43      (![X9 : $i, X10 : $i]:
% 1.20/1.43         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 1.20/1.43      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.20/1.43  thf('44', plain,
% 1.20/1.43      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.20/1.43      inference('sup-', [status(thm)], ['42', '43'])).
% 1.20/1.43  thf(t100_xboole_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]:
% 1.20/1.43     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.20/1.43  thf('45', plain,
% 1.20/1.43      (![X7 : $i, X8 : $i]:
% 1.20/1.43         ((k4_xboole_0 @ X7 @ X8)
% 1.20/1.43           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.20/1.43      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.20/1.43  thf('46', plain,
% 1.20/1.43      (![X0 : $i]:
% 1.20/1.43         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.20/1.43           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.20/1.43      inference('sup+', [status(thm)], ['44', '45'])).
% 1.20/1.43  thf('47', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.20/1.43      inference('cnf', [status(esa)], [t3_boole])).
% 1.20/1.43  thf('48', plain,
% 1.20/1.43      (![X7 : $i, X8 : $i]:
% 1.20/1.43         ((k4_xboole_0 @ X7 @ X8)
% 1.20/1.43           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.20/1.43      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.20/1.43  thf('49', plain,
% 1.20/1.43      (![X0 : $i]:
% 1.20/1.43         ((X0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.20/1.43      inference('sup+', [status(thm)], ['47', '48'])).
% 1.20/1.43  thf(commutativity_k2_tarski, axiom,
% 1.20/1.43    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.20/1.43  thf('50', plain,
% 1.20/1.43      (![X19 : $i, X20 : $i]:
% 1.20/1.43         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 1.20/1.43      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.20/1.43  thf(t12_setfam_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]:
% 1.20/1.43     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.20/1.43  thf('51', plain,
% 1.20/1.43      (![X39 : $i, X40 : $i]:
% 1.20/1.43         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 1.20/1.43      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.20/1.43  thf('52', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]:
% 1.20/1.43         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.20/1.43      inference('sup+', [status(thm)], ['50', '51'])).
% 1.20/1.43  thf('53', plain,
% 1.20/1.43      (![X39 : $i, X40 : $i]:
% 1.20/1.43         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 1.20/1.43      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.20/1.43  thf('54', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.20/1.43      inference('sup+', [status(thm)], ['52', '53'])).
% 1.20/1.43  thf('55', plain,
% 1.20/1.43      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.20/1.43      inference('sup-', [status(thm)], ['42', '43'])).
% 1.20/1.43  thf('56', plain,
% 1.20/1.43      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.20/1.43      inference('sup+', [status(thm)], ['54', '55'])).
% 1.20/1.43  thf('57', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.20/1.43      inference('demod', [status(thm)], ['49', '56'])).
% 1.20/1.43  thf('58', plain,
% 1.20/1.43      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.20/1.43      inference('demod', [status(thm)], ['46', '57'])).
% 1.20/1.43  thf('59', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]:
% 1.20/1.43         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.20/1.43          | ((X1) = (k1_xboole_0)))),
% 1.20/1.43      inference('demod', [status(thm)], ['41', '58'])).
% 1.20/1.43  thf('60', plain,
% 1.20/1.43      (![X0 : $i]:
% 1.20/1.43         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.20/1.43           = (k4_xboole_0 @ sk_B @ X0))),
% 1.20/1.43      inference('sup-', [status(thm)], ['16', '17'])).
% 1.20/1.43  thf('61', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43             (k1_tops_1 @ sk_A @ sk_B))))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('split', [status(esa)], ['2'])).
% 1.20/1.43  thf('62', plain,
% 1.20/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('sup+', [status(thm)], ['60', '61'])).
% 1.20/1.43  thf(t36_xboole_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.20/1.43  thf('63', plain,
% 1.20/1.43      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.20/1.43      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.20/1.43  thf('64', plain,
% 1.20/1.43      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('sup+', [status(thm)], ['62', '63'])).
% 1.20/1.43  thf('65', plain,
% 1.20/1.43      (![X9 : $i, X10 : $i]:
% 1.20/1.43         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 1.20/1.43      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.20/1.43  thf('66', plain,
% 1.20/1.43      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.20/1.43          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('sup-', [status(thm)], ['64', '65'])).
% 1.20/1.43  thf('67', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.20/1.43      inference('sup+', [status(thm)], ['52', '53'])).
% 1.20/1.43  thf('68', plain,
% 1.20/1.43      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.20/1.43          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('demod', [status(thm)], ['66', '67'])).
% 1.20/1.43  thf('69', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.20/1.43      inference('sup+', [status(thm)], ['52', '53'])).
% 1.20/1.43  thf(t48_xboole_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]:
% 1.20/1.43     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.20/1.43  thf('70', plain,
% 1.20/1.43      (![X15 : $i, X16 : $i]:
% 1.20/1.43         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.20/1.43           = (k3_xboole_0 @ X15 @ X16))),
% 1.20/1.43      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.20/1.43  thf('71', plain,
% 1.20/1.43      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.20/1.43         (~ (r2_hidden @ X4 @ X2)
% 1.20/1.43          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.20/1.43      inference('simplify', [status(thm)], ['37'])).
% 1.20/1.43  thf('72', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.43         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.20/1.43          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.20/1.43      inference('sup-', [status(thm)], ['70', '71'])).
% 1.20/1.43  thf('73', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.43         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.20/1.43          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.20/1.43      inference('sup-', [status(thm)], ['69', '72'])).
% 1.20/1.43  thf('74', plain,
% 1.20/1.43      ((![X0 : $i]:
% 1.20/1.43          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 1.20/1.43           | ~ (r2_hidden @ X0 @ 
% 1.20/1.43                (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('sup-', [status(thm)], ['68', '73'])).
% 1.20/1.43  thf('75', plain,
% 1.20/1.43      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.20/1.43         (~ (r2_hidden @ X4 @ X3)
% 1.20/1.43          | (r2_hidden @ X4 @ X1)
% 1.20/1.43          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.20/1.43      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.20/1.43  thf('76', plain,
% 1.20/1.43      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.20/1.43         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.20/1.43      inference('simplify', [status(thm)], ['75'])).
% 1.20/1.43  thf('77', plain,
% 1.20/1.43      ((![X0 : $i]:
% 1.20/1.43          ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('clc', [status(thm)], ['74', '76'])).
% 1.20/1.43  thf('78', plain,
% 1.20/1.43      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('sup-', [status(thm)], ['59', '77'])).
% 1.20/1.43  thf(t98_xboole_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]:
% 1.20/1.43     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.20/1.43  thf('79', plain,
% 1.20/1.43      (![X17 : $i, X18 : $i]:
% 1.20/1.43         ((k2_xboole_0 @ X17 @ X18)
% 1.20/1.43           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 1.20/1.43      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.20/1.43  thf('80', plain,
% 1.20/1.43      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.20/1.43          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('sup+', [status(thm)], ['78', '79'])).
% 1.20/1.43  thf('81', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.20/1.43      inference('demod', [status(thm)], ['49', '56'])).
% 1.20/1.43  thf('82', plain,
% 1.20/1.43      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('demod', [status(thm)], ['80', '81'])).
% 1.20/1.43  thf('83', plain,
% 1.20/1.43      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.20/1.43          = (sk_B)))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('demod', [status(thm)], ['34', '82'])).
% 1.20/1.43  thf('84', plain,
% 1.20/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf(t65_tops_1, axiom,
% 1.20/1.43    (![A:$i]:
% 1.20/1.43     ( ( l1_pre_topc @ A ) =>
% 1.20/1.43       ( ![B:$i]:
% 1.20/1.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.43           ( ( k2_pre_topc @ A @ B ) =
% 1.20/1.43             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.20/1.43  thf('85', plain,
% 1.20/1.43      (![X52 : $i, X53 : $i]:
% 1.20/1.43         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 1.20/1.43          | ((k2_pre_topc @ X53 @ X52)
% 1.20/1.43              = (k4_subset_1 @ (u1_struct_0 @ X53) @ X52 @ 
% 1.20/1.43                 (k2_tops_1 @ X53 @ X52)))
% 1.20/1.43          | ~ (l1_pre_topc @ X53))),
% 1.20/1.43      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.20/1.43  thf('86', plain,
% 1.20/1.43      ((~ (l1_pre_topc @ sk_A)
% 1.20/1.43        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.20/1.43            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.20/1.43      inference('sup-', [status(thm)], ['84', '85'])).
% 1.20/1.43  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf('88', plain,
% 1.20/1.43      (((k2_pre_topc @ sk_A @ sk_B)
% 1.20/1.43         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.20/1.43      inference('demod', [status(thm)], ['86', '87'])).
% 1.20/1.43  thf('89', plain,
% 1.20/1.43      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('sup+', [status(thm)], ['83', '88'])).
% 1.20/1.43  thf('90', plain,
% 1.20/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf(fc1_tops_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]:
% 1.20/1.43     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.20/1.43         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.20/1.43       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.20/1.43  thf('91', plain,
% 1.20/1.43      (![X46 : $i, X47 : $i]:
% 1.20/1.43         (~ (l1_pre_topc @ X46)
% 1.20/1.43          | ~ (v2_pre_topc @ X46)
% 1.20/1.43          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 1.20/1.43          | (v4_pre_topc @ (k2_pre_topc @ X46 @ X47) @ X46))),
% 1.20/1.43      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.20/1.43  thf('92', plain,
% 1.20/1.43      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.20/1.43        | ~ (v2_pre_topc @ sk_A)
% 1.20/1.43        | ~ (l1_pre_topc @ sk_A))),
% 1.20/1.43      inference('sup-', [status(thm)], ['90', '91'])).
% 1.20/1.43  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf('95', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.20/1.43      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.20/1.43  thf('96', plain,
% 1.20/1.43      (((v4_pre_topc @ sk_B @ sk_A))
% 1.20/1.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.43      inference('sup+', [status(thm)], ['89', '95'])).
% 1.20/1.43  thf('97', plain,
% 1.20/1.43      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.20/1.43      inference('split', [status(esa)], ['0'])).
% 1.20/1.43  thf('98', plain,
% 1.20/1.43      (~
% 1.20/1.43       (((k2_tops_1 @ sk_A @ sk_B)
% 1.20/1.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.20/1.43             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.20/1.43       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.20/1.43      inference('sup-', [status(thm)], ['96', '97'])).
% 1.20/1.43  thf('99', plain, ($false),
% 1.20/1.43      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '98'])).
% 1.20/1.43  
% 1.20/1.43  % SZS output end Refutation
% 1.20/1.43  
% 1.20/1.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
