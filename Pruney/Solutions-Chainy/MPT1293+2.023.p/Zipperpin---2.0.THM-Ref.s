%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YTSBwpm3tU

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:09 EST 2020

% Result     : Theorem 32.92s
% Output     : Refutation 32.92s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 211 expanded)
%              Number of leaves         :   35 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          : 1303 (3470 expanded)
%              Number of equality atoms :   51 (  67 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t6_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tops_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k5_setfam_1 @ X42 @ X41 )
        = ( k3_tarski @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('3',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k5_setfam_1 @ X42 @ X41 )
        = ( k3_tarski @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('6',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
    = ( k3_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X23 @ X22 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k5_setfam_1 @ X42 @ X41 )
        = ( k3_tarski @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k7_subset_1 @ X31 @ X30 @ X32 )
        = ( k4_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('20',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('22',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k7_subset_1 @ X31 @ X30 @ X32 )
        = ( k4_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('28',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('32',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X37 @ X38 ) @ ( k3_subset_1 @ X37 @ ( k9_subset_1 @ X37 @ X38 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k9_subset_1 @ X35 @ X33 @ X34 )
        = ( k3_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    r1_tarski @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_xboole_0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('40',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X26 @ ( k3_subset_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('44',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('47',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X20 @ X19 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('58',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k4_subset_1 @ X28 @ X27 @ X29 )
        = ( k2_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('63',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('66',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X26 @ ( k3_subset_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('67',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['38','41','64','67'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('69',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X8 ) @ ( k3_tarski @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('70',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('73',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_subset_1 @ X13 @ X14 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
        = ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C )
    = ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('77',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k4_subset_1 @ X28 @ X27 @ X29 )
        = ( k2_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('85',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X10 ) @ ( k3_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('86',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['70','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['25','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YTSBwpm3tU
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:08:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 32.92/33.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 32.92/33.15  % Solved by: fo/fo7.sh
% 32.92/33.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.92/33.15  % done 6614 iterations in 32.686s
% 32.92/33.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 32.92/33.15  % SZS output start Refutation
% 32.92/33.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 32.92/33.15  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 32.92/33.15  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 32.92/33.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 32.92/33.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 32.92/33.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 32.92/33.15  thf(sk_A_type, type, sk_A: $i).
% 32.92/33.15  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 32.92/33.15  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 32.92/33.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 32.92/33.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 32.92/33.15  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 32.92/33.15  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 32.92/33.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 32.92/33.15  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 32.92/33.15  thf(sk_B_type, type, sk_B: $i).
% 32.92/33.15  thf(sk_C_type, type, sk_C: $i).
% 32.92/33.15  thf(t6_tops_2, conjecture,
% 32.92/33.15    (![A:$i]:
% 32.92/33.15     ( ( l1_struct_0 @ A ) =>
% 32.92/33.15       ( ![B:$i]:
% 32.92/33.15         ( ( m1_subset_1 @
% 32.92/33.15             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 32.92/33.15           ( ![C:$i]:
% 32.92/33.15             ( ( m1_subset_1 @
% 32.92/33.15                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 32.92/33.15               ( r1_tarski @
% 32.92/33.15                 ( k7_subset_1 @
% 32.92/33.15                   ( u1_struct_0 @ A ) @ 
% 32.92/33.15                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 32.92/33.15                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 32.92/33.15                 ( k5_setfam_1 @
% 32.92/33.15                   ( u1_struct_0 @ A ) @ 
% 32.92/33.15                   ( k7_subset_1 @
% 32.92/33.15                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 32.92/33.15  thf(zf_stmt_0, negated_conjecture,
% 32.92/33.15    (~( ![A:$i]:
% 32.92/33.15        ( ( l1_struct_0 @ A ) =>
% 32.92/33.15          ( ![B:$i]:
% 32.92/33.15            ( ( m1_subset_1 @
% 32.92/33.15                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 32.92/33.15              ( ![C:$i]:
% 32.92/33.15                ( ( m1_subset_1 @
% 32.92/33.15                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 32.92/33.15                  ( r1_tarski @
% 32.92/33.15                    ( k7_subset_1 @
% 32.92/33.15                      ( u1_struct_0 @ A ) @ 
% 32.92/33.15                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 32.92/33.15                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 32.92/33.15                    ( k5_setfam_1 @
% 32.92/33.15                      ( u1_struct_0 @ A ) @ 
% 32.92/33.15                      ( k7_subset_1 @
% 32.92/33.15                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 32.92/33.15    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 32.92/33.15  thf('0', plain,
% 32.92/33.15      (~ (r1_tarski @ 
% 32.92/33.15          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.92/33.15           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 32.92/33.15           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 32.92/33.15          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 32.92/33.15           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf('1', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_B @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf(redefinition_k5_setfam_1, axiom,
% 32.92/33.15    (![A:$i,B:$i]:
% 32.92/33.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 32.92/33.15       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 32.92/33.15  thf('2', plain,
% 32.92/33.15      (![X41 : $i, X42 : $i]:
% 32.92/33.15         (((k5_setfam_1 @ X42 @ X41) = (k3_tarski @ X41))
% 32.92/33.15          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X42))))),
% 32.92/33.15      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 32.92/33.15  thf('3', plain,
% 32.92/33.15      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 32.92/33.15      inference('sup-', [status(thm)], ['1', '2'])).
% 32.92/33.15  thf('4', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_C @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf('5', plain,
% 32.92/33.15      (![X41 : $i, X42 : $i]:
% 32.92/33.15         (((k5_setfam_1 @ X42 @ X41) = (k3_tarski @ X41))
% 32.92/33.15          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X42))))),
% 32.92/33.15      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 32.92/33.15  thf('6', plain,
% 32.92/33.15      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 32.92/33.15      inference('sup-', [status(thm)], ['4', '5'])).
% 32.92/33.15  thf('7', plain,
% 32.92/33.15      (~ (r1_tarski @ 
% 32.92/33.15          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 32.92/33.15           (k3_tarski @ sk_C)) @ 
% 32.92/33.15          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 32.92/33.15           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 32.92/33.15      inference('demod', [status(thm)], ['0', '3', '6'])).
% 32.92/33.15  thf('8', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_B @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf(dt_k7_subset_1, axiom,
% 32.92/33.15    (![A:$i,B:$i,C:$i]:
% 32.92/33.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 32.92/33.15       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 32.92/33.15  thf('9', plain,
% 32.92/33.15      (![X22 : $i, X23 : $i, X24 : $i]:
% 32.92/33.15         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 32.92/33.15          | (m1_subset_1 @ (k7_subset_1 @ X23 @ X22 @ X24) @ 
% 32.92/33.15             (k1_zfmisc_1 @ X23)))),
% 32.92/33.15      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 32.92/33.15  thf('10', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         (m1_subset_1 @ 
% 32.92/33.15          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0) @ 
% 32.92/33.15          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['8', '9'])).
% 32.92/33.15  thf('11', plain,
% 32.92/33.15      (![X41 : $i, X42 : $i]:
% 32.92/33.15         (((k5_setfam_1 @ X42 @ X41) = (k3_tarski @ X41))
% 32.92/33.15          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X42))))),
% 32.92/33.15      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 32.92/33.15  thf('12', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 32.92/33.15           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0))
% 32.92/33.15           = (k3_tarski @ 
% 32.92/33.15              (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)))),
% 32.92/33.15      inference('sup-', [status(thm)], ['10', '11'])).
% 32.92/33.15  thf('13', plain,
% 32.92/33.15      (~ (r1_tarski @ 
% 32.92/33.15          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 32.92/33.15           (k3_tarski @ sk_C)) @ 
% 32.92/33.15          (k3_tarski @ 
% 32.92/33.15           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 32.92/33.15      inference('demod', [status(thm)], ['7', '12'])).
% 32.92/33.15  thf('14', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_B @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf(redefinition_k7_subset_1, axiom,
% 32.92/33.15    (![A:$i,B:$i,C:$i]:
% 32.92/33.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 32.92/33.15       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 32.92/33.15  thf('15', plain,
% 32.92/33.15      (![X30 : $i, X31 : $i, X32 : $i]:
% 32.92/33.15         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 32.92/33.15          | ((k7_subset_1 @ X31 @ X30 @ X32) = (k4_xboole_0 @ X30 @ X32)))),
% 32.92/33.15      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 32.92/33.15  thf('16', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 32.92/33.15           = (k4_xboole_0 @ sk_B @ X0))),
% 32.92/33.15      inference('sup-', [status(thm)], ['14', '15'])).
% 32.92/33.15  thf('17', plain,
% 32.92/33.15      (~ (r1_tarski @ 
% 32.92/33.15          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 32.92/33.15           (k3_tarski @ sk_C)) @ 
% 32.92/33.15          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 32.92/33.15      inference('demod', [status(thm)], ['13', '16'])).
% 32.92/33.15  thf('18', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_B @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf(dt_k5_setfam_1, axiom,
% 32.92/33.15    (![A:$i,B:$i]:
% 32.92/33.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 32.92/33.15       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 32.92/33.15  thf('19', plain,
% 32.92/33.15      (![X39 : $i, X40 : $i]:
% 32.92/33.15         ((m1_subset_1 @ (k5_setfam_1 @ X39 @ X40) @ (k1_zfmisc_1 @ X39))
% 32.92/33.15          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X39))))),
% 32.92/33.15      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 32.92/33.15  thf('20', plain,
% 32.92/33.15      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 32.92/33.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.92/33.15      inference('sup-', [status(thm)], ['18', '19'])).
% 32.92/33.15  thf('21', plain,
% 32.92/33.15      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 32.92/33.15      inference('sup-', [status(thm)], ['1', '2'])).
% 32.92/33.15  thf('22', plain,
% 32.92/33.15      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.92/33.15      inference('demod', [status(thm)], ['20', '21'])).
% 32.92/33.15  thf('23', plain,
% 32.92/33.15      (![X30 : $i, X31 : $i, X32 : $i]:
% 32.92/33.15         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 32.92/33.15          | ((k7_subset_1 @ X31 @ X30 @ X32) = (k4_xboole_0 @ X30 @ X32)))),
% 32.92/33.15      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 32.92/33.15  thf('24', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 32.92/33.15           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 32.92/33.15      inference('sup-', [status(thm)], ['22', '23'])).
% 32.92/33.15  thf('25', plain,
% 32.92/33.15      (~ (r1_tarski @ 
% 32.92/33.15          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 32.92/33.15          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 32.92/33.15      inference('demod', [status(thm)], ['17', '24'])).
% 32.92/33.15  thf('26', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_B @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf(dt_k3_subset_1, axiom,
% 32.92/33.15    (![A:$i,B:$i]:
% 32.92/33.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 32.92/33.15       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 32.92/33.15  thf('27', plain,
% 32.92/33.15      (![X17 : $i, X18 : $i]:
% 32.92/33.15         ((m1_subset_1 @ (k3_subset_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 32.92/33.15          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 32.92/33.15      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 32.92/33.15  thf('28', plain,
% 32.92/33.15      ((m1_subset_1 @ 
% 32.92/33.15        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['26', '27'])).
% 32.92/33.15  thf('29', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_C @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf('30', plain,
% 32.92/33.15      (![X17 : $i, X18 : $i]:
% 32.92/33.15         ((m1_subset_1 @ (k3_subset_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 32.92/33.15          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 32.92/33.15      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 32.92/33.15  thf('31', plain,
% 32.92/33.15      ((m1_subset_1 @ 
% 32.92/33.15        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C) @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['29', '30'])).
% 32.92/33.15  thf(t42_subset_1, axiom,
% 32.92/33.15    (![A:$i,B:$i]:
% 32.92/33.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 32.92/33.15       ( ![C:$i]:
% 32.92/33.15         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 32.92/33.15           ( r1_tarski @
% 32.92/33.15             ( k3_subset_1 @ A @ B ) @ 
% 32.92/33.15             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 32.92/33.15  thf('32', plain,
% 32.92/33.15      (![X36 : $i, X37 : $i, X38 : $i]:
% 32.92/33.15         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 32.92/33.15          | (r1_tarski @ (k3_subset_1 @ X37 @ X38) @ 
% 32.92/33.15             (k3_subset_1 @ X37 @ (k9_subset_1 @ X37 @ X38 @ X36)))
% 32.92/33.15          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 32.92/33.15      inference('cnf', [status(esa)], [t42_subset_1])).
% 32.92/33.15  thf('33', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         (~ (m1_subset_1 @ X0 @ 
% 32.92/33.15             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 32.92/33.15          | (r1_tarski @ 
% 32.92/33.15             (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0) @ 
% 32.92/33.15             (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15              (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ 
% 32.92/33.15               (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['31', '32'])).
% 32.92/33.15  thf('34', plain,
% 32.92/33.15      ((m1_subset_1 @ 
% 32.92/33.15        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C) @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['29', '30'])).
% 32.92/33.15  thf(redefinition_k9_subset_1, axiom,
% 32.92/33.15    (![A:$i,B:$i,C:$i]:
% 32.92/33.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 32.92/33.15       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 32.92/33.15  thf('35', plain,
% 32.92/33.15      (![X33 : $i, X34 : $i, X35 : $i]:
% 32.92/33.15         (((k9_subset_1 @ X35 @ X33 @ X34) = (k3_xboole_0 @ X33 @ X34))
% 32.92/33.15          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 32.92/33.15      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 32.92/33.15  thf('36', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ 
% 32.92/33.15           (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))
% 32.92/33.15           = (k3_xboole_0 @ X0 @ 
% 32.92/33.15              (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))),
% 32.92/33.15      inference('sup-', [status(thm)], ['34', '35'])).
% 32.92/33.15  thf('37', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         (~ (m1_subset_1 @ X0 @ 
% 32.92/33.15             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 32.92/33.15          | (r1_tarski @ 
% 32.92/33.15             (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0) @ 
% 32.92/33.15             (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15              (k3_xboole_0 @ X0 @ 
% 32.92/33.15               (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))))),
% 32.92/33.15      inference('demod', [status(thm)], ['33', '36'])).
% 32.92/33.15  thf('38', plain,
% 32.92/33.15      ((r1_tarski @ 
% 32.92/33.15        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15         (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B)) @ 
% 32.92/33.15        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15         (k3_xboole_0 @ 
% 32.92/33.15          (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 32.92/33.15          (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['28', '37'])).
% 32.92/33.15  thf('39', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_B @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf(involutiveness_k3_subset_1, axiom,
% 32.92/33.15    (![A:$i,B:$i]:
% 32.92/33.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 32.92/33.15       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 32.92/33.15  thf('40', plain,
% 32.92/33.15      (![X25 : $i, X26 : $i]:
% 32.92/33.15         (((k3_subset_1 @ X26 @ (k3_subset_1 @ X26 @ X25)) = (X25))
% 32.92/33.15          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 32.92/33.15      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 32.92/33.15  thf('41', plain,
% 32.92/33.15      (((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15         (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B)) = (
% 32.92/33.15         sk_B))),
% 32.92/33.15      inference('sup-', [status(thm)], ['39', '40'])).
% 32.92/33.15  thf('42', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_C @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf(d5_subset_1, axiom,
% 32.92/33.15    (![A:$i,B:$i]:
% 32.92/33.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 32.92/33.15       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 32.92/33.15  thf('43', plain,
% 32.92/33.15      (![X15 : $i, X16 : $i]:
% 32.92/33.15         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 32.92/33.15          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 32.92/33.15      inference('cnf', [status(esa)], [d5_subset_1])).
% 32.92/33.15  thf('44', plain,
% 32.92/33.15      (((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)
% 32.92/33.15         = (k4_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))),
% 32.92/33.15      inference('sup-', [status(thm)], ['42', '43'])).
% 32.92/33.15  thf('45', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_B @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf('46', plain,
% 32.92/33.15      (![X15 : $i, X16 : $i]:
% 32.92/33.15         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 32.92/33.15          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 32.92/33.15      inference('cnf', [status(esa)], [d5_subset_1])).
% 32.92/33.15  thf('47', plain,
% 32.92/33.15      (((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 32.92/33.15         = (k4_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B))),
% 32.92/33.15      inference('sup-', [status(thm)], ['45', '46'])).
% 32.92/33.15  thf(t53_xboole_1, axiom,
% 32.92/33.15    (![A:$i,B:$i,C:$i]:
% 32.92/33.15     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 32.92/33.15       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 32.92/33.15  thf('48', plain,
% 32.92/33.15      (![X5 : $i, X6 : $i, X7 : $i]:
% 32.92/33.15         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 32.92/33.15           = (k3_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X7)))),
% 32.92/33.15      inference('cnf', [status(esa)], [t53_xboole_1])).
% 32.92/33.15  thf('49', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         ((k4_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15           (k2_xboole_0 @ sk_B @ X0))
% 32.92/33.15           = (k3_xboole_0 @ 
% 32.92/33.15              (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 32.92/33.15              (k4_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0)))),
% 32.92/33.15      inference('sup+', [status(thm)], ['47', '48'])).
% 32.92/33.15  thf('50', plain,
% 32.92/33.15      (((k4_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15         (k2_xboole_0 @ sk_B @ sk_C))
% 32.92/33.15         = (k3_xboole_0 @ 
% 32.92/33.15            (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 32.92/33.15            (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))),
% 32.92/33.15      inference('sup+', [status(thm)], ['44', '49'])).
% 32.92/33.15  thf('51', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_C @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf('52', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_B @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf(dt_k4_subset_1, axiom,
% 32.92/33.15    (![A:$i,B:$i,C:$i]:
% 32.92/33.15     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 32.92/33.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 32.92/33.15       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 32.92/33.15  thf('53', plain,
% 32.92/33.15      (![X19 : $i, X20 : $i, X21 : $i]:
% 32.92/33.15         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 32.92/33.15          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 32.92/33.15          | (m1_subset_1 @ (k4_subset_1 @ X20 @ X19 @ X21) @ 
% 32.92/33.15             (k1_zfmisc_1 @ X20)))),
% 32.92/33.15      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 32.92/33.15  thf('54', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         ((m1_subset_1 @ 
% 32.92/33.15           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0) @ 
% 32.92/33.15           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 32.92/33.15          | ~ (m1_subset_1 @ X0 @ 
% 32.92/33.15               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['52', '53'])).
% 32.92/33.15  thf('55', plain,
% 32.92/33.15      ((m1_subset_1 @ 
% 32.92/33.15        (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['51', '54'])).
% 32.92/33.15  thf('56', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_C @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf('57', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_B @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf(redefinition_k4_subset_1, axiom,
% 32.92/33.15    (![A:$i,B:$i,C:$i]:
% 32.92/33.15     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 32.92/33.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 32.92/33.15       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 32.92/33.15  thf('58', plain,
% 32.92/33.15      (![X27 : $i, X28 : $i, X29 : $i]:
% 32.92/33.15         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 32.92/33.15          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28))
% 32.92/33.15          | ((k4_subset_1 @ X28 @ X27 @ X29) = (k2_xboole_0 @ X27 @ X29)))),
% 32.92/33.15      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 32.92/33.15  thf('59', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 32.92/33.15            = (k2_xboole_0 @ sk_B @ X0))
% 32.92/33.15          | ~ (m1_subset_1 @ X0 @ 
% 32.92/33.15               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['57', '58'])).
% 32.92/33.15  thf('60', plain,
% 32.92/33.15      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)
% 32.92/33.15         = (k2_xboole_0 @ sk_B @ sk_C))),
% 32.92/33.15      inference('sup-', [status(thm)], ['56', '59'])).
% 32.92/33.15  thf('61', plain,
% 32.92/33.15      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('demod', [status(thm)], ['55', '60'])).
% 32.92/33.15  thf('62', plain,
% 32.92/33.15      (![X15 : $i, X16 : $i]:
% 32.92/33.15         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 32.92/33.15          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 32.92/33.15      inference('cnf', [status(esa)], [d5_subset_1])).
% 32.92/33.15  thf('63', plain,
% 32.92/33.15      (((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15         (k2_xboole_0 @ sk_B @ sk_C))
% 32.92/33.15         = (k4_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15            (k2_xboole_0 @ sk_B @ sk_C)))),
% 32.92/33.15      inference('sup-', [status(thm)], ['61', '62'])).
% 32.92/33.15  thf('64', plain,
% 32.92/33.15      (((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15         (k2_xboole_0 @ sk_B @ sk_C))
% 32.92/33.15         = (k3_xboole_0 @ 
% 32.92/33.15            (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 32.92/33.15            (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))),
% 32.92/33.15      inference('demod', [status(thm)], ['50', '63'])).
% 32.92/33.15  thf('65', plain,
% 32.92/33.15      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('demod', [status(thm)], ['55', '60'])).
% 32.92/33.15  thf('66', plain,
% 32.92/33.15      (![X25 : $i, X26 : $i]:
% 32.92/33.15         (((k3_subset_1 @ X26 @ (k3_subset_1 @ X26 @ X25)) = (X25))
% 32.92/33.15          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 32.92/33.15      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 32.92/33.15  thf('67', plain,
% 32.92/33.15      (((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15         (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 32.92/33.15          (k2_xboole_0 @ sk_B @ sk_C)))
% 32.92/33.15         = (k2_xboole_0 @ sk_B @ sk_C))),
% 32.92/33.15      inference('sup-', [status(thm)], ['65', '66'])).
% 32.92/33.15  thf('68', plain, ((r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))),
% 32.92/33.15      inference('demod', [status(thm)], ['38', '41', '64', '67'])).
% 32.92/33.15  thf(t95_zfmisc_1, axiom,
% 32.92/33.15    (![A:$i,B:$i]:
% 32.92/33.15     ( ( r1_tarski @ A @ B ) =>
% 32.92/33.15       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 32.92/33.15  thf('69', plain,
% 32.92/33.15      (![X8 : $i, X9 : $i]:
% 32.92/33.15         ((r1_tarski @ (k3_tarski @ X8) @ (k3_tarski @ X9))
% 32.92/33.15          | ~ (r1_tarski @ X8 @ X9))),
% 32.92/33.15      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 32.92/33.15  thf('70', plain,
% 32.92/33.15      ((r1_tarski @ (k3_tarski @ sk_B) @ 
% 32.92/33.15        (k3_tarski @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 32.92/33.15      inference('sup-', [status(thm)], ['68', '69'])).
% 32.92/33.15  thf('71', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_C @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf('72', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_B @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf(commutativity_k4_subset_1, axiom,
% 32.92/33.15    (![A:$i,B:$i,C:$i]:
% 32.92/33.15     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 32.92/33.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 32.92/33.15       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 32.92/33.15  thf('73', plain,
% 32.92/33.15      (![X12 : $i, X13 : $i, X14 : $i]:
% 32.92/33.15         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 32.92/33.15          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 32.92/33.15          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k4_subset_1 @ X13 @ X14 @ X12)))),
% 32.92/33.15      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 32.92/33.15  thf('74', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 32.92/33.15            = (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B))
% 32.92/33.15          | ~ (m1_subset_1 @ X0 @ 
% 32.92/33.15               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['72', '73'])).
% 32.92/33.15  thf('75', plain,
% 32.92/33.15      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)
% 32.92/33.15         = (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ sk_B))),
% 32.92/33.15      inference('sup-', [status(thm)], ['71', '74'])).
% 32.92/33.15  thf('76', plain,
% 32.92/33.15      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)
% 32.92/33.15         = (k2_xboole_0 @ sk_B @ sk_C))),
% 32.92/33.15      inference('sup-', [status(thm)], ['56', '59'])).
% 32.92/33.15  thf('77', plain,
% 32.92/33.15      (((k2_xboole_0 @ sk_B @ sk_C)
% 32.92/33.15         = (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ sk_B))),
% 32.92/33.15      inference('demod', [status(thm)], ['75', '76'])).
% 32.92/33.15  thf('78', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_B @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf('79', plain,
% 32.92/33.15      ((m1_subset_1 @ sk_C @ 
% 32.92/33.15        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 32.92/33.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.92/33.15  thf('80', plain,
% 32.92/33.15      (![X27 : $i, X28 : $i, X29 : $i]:
% 32.92/33.15         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 32.92/33.15          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28))
% 32.92/33.15          | ((k4_subset_1 @ X28 @ X27 @ X29) = (k2_xboole_0 @ X27 @ X29)))),
% 32.92/33.15      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 32.92/33.15  thf('81', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ X0)
% 32.92/33.15            = (k2_xboole_0 @ sk_C @ X0))
% 32.92/33.15          | ~ (m1_subset_1 @ X0 @ 
% 32.92/33.15               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['79', '80'])).
% 32.92/33.15  thf('82', plain,
% 32.92/33.15      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ sk_B)
% 32.92/33.15         = (k2_xboole_0 @ sk_C @ sk_B))),
% 32.92/33.15      inference('sup-', [status(thm)], ['78', '81'])).
% 32.92/33.15  thf('83', plain,
% 32.92/33.15      (((k2_xboole_0 @ sk_B @ sk_C) = (k2_xboole_0 @ sk_C @ sk_B))),
% 32.92/33.15      inference('sup+', [status(thm)], ['77', '82'])).
% 32.92/33.15  thf(t39_xboole_1, axiom,
% 32.92/33.15    (![A:$i,B:$i]:
% 32.92/33.15     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 32.92/33.15  thf('84', plain,
% 32.92/33.15      (![X0 : $i, X1 : $i]:
% 32.92/33.15         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 32.92/33.15           = (k2_xboole_0 @ X0 @ X1))),
% 32.92/33.15      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.92/33.15  thf(t96_zfmisc_1, axiom,
% 32.92/33.15    (![A:$i,B:$i]:
% 32.92/33.15     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 32.92/33.15       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 32.92/33.15  thf('85', plain,
% 32.92/33.15      (![X10 : $i, X11 : $i]:
% 32.92/33.15         ((k3_tarski @ (k2_xboole_0 @ X10 @ X11))
% 32.92/33.15           = (k2_xboole_0 @ (k3_tarski @ X10) @ (k3_tarski @ X11)))),
% 32.92/33.15      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 32.92/33.15  thf(t43_xboole_1, axiom,
% 32.92/33.15    (![A:$i,B:$i,C:$i]:
% 32.92/33.15     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 32.92/33.15       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 32.92/33.15  thf('86', plain,
% 32.92/33.15      (![X2 : $i, X3 : $i, X4 : $i]:
% 32.92/33.15         ((r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 32.92/33.15          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 32.92/33.15      inference('cnf', [status(esa)], [t43_xboole_1])).
% 32.92/33.15  thf('87', plain,
% 32.92/33.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.92/33.15         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 32.92/33.15          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 32.92/33.15             (k3_tarski @ X0)))),
% 32.92/33.15      inference('sup-', [status(thm)], ['85', '86'])).
% 32.92/33.15  thf('88', plain,
% 32.92/33.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.92/33.15         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 32.92/33.15          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 32.92/33.15             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['84', '87'])).
% 32.92/33.15  thf('89', plain,
% 32.92/33.15      (![X0 : $i]:
% 32.92/33.15         (~ (r1_tarski @ X0 @ (k3_tarski @ (k2_xboole_0 @ sk_B @ sk_C)))
% 32.92/33.15          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_tarski @ sk_C)) @ 
% 32.92/33.15             (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 32.92/33.15      inference('sup-', [status(thm)], ['83', '88'])).
% 32.92/33.15  thf('90', plain,
% 32.92/33.15      ((r1_tarski @ (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 32.92/33.15        (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 32.92/33.15      inference('sup-', [status(thm)], ['70', '89'])).
% 32.92/33.15  thf('91', plain, ($false), inference('demod', [status(thm)], ['25', '90'])).
% 32.92/33.15  
% 32.92/33.15  % SZS output end Refutation
% 32.92/33.15  
% 32.92/33.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
