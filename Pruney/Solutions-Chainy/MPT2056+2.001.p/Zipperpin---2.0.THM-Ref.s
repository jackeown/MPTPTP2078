%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PRg7GBw3wJ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 177 expanded)
%              Number of leaves         :   45 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  888 (2178 expanded)
%              Number of equality atoms :   55 ( 107 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(t15_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( B
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
           => ( B
              = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_yellow19])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('2',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X30: $i] :
      ( ( k9_setfam_1 @ X30 )
      = ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('4',plain,
    ( ( k9_setfam_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X18 ) @ X19 )
      | ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k9_setfam_1 @ k1_xboole_0 ) @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('7',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ ( k9_setfam_1 @ k1_xboole_0 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k9_setfam_1 @ k1_xboole_0 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k9_setfam_1 @ k1_xboole_0 ) )
        = X0 )
      | ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X30: $i] :
      ( ( k9_setfam_1 @ X30 )
      = ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('23',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t4_waybel_7,axiom,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf('24',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('25',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t2_yellow19,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
         => ! [C: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( v1_xboole_0 @ C ) ) ) ) )).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ X38 ) ) )
      | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ X38 ) )
      | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X38 ) ) ) )
      | ~ ( r2_hidden @ X39 @ X37 )
      | ~ ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('27',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('28',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('29',plain,(
    ! [X30: $i] :
      ( ( k9_setfam_1 @ X30 )
      = ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('30',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( v1_subset_1 @ X37 @ ( k9_setfam_1 @ X38 ) )
      | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ X38 ) )
      | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X38 ) ) )
      | ~ ( r2_hidden @ X39 @ X37 )
      | ~ ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('36',plain,(
    v1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['31','32','33','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_B_2 @ ( k9_setfam_1 @ k1_xboole_0 ) )
      = sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','37'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ sk_B_2 @ ( k9_setfam_1 @ k1_xboole_0 ) )
      = sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    sk_B_2
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t14_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ ( k1_tarski @ k1_xboole_0 ) )
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('43',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( v2_waybel_0 @ X35 @ ( k3_yellow_1 @ ( k2_struct_0 @ X36 ) ) )
      | ~ ( v13_waybel_0 @ X35 @ ( k3_yellow_1 @ ( k2_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X36 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X36 ) ) ) @ X35 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X36 @ ( k3_yellow19 @ X36 @ ( k2_struct_0 @ X36 ) @ X35 ) ) )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('44',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('45',plain,(
    ! [X30: $i] :
      ( ( k9_setfam_1 @ X30 )
      = ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('46',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('47',plain,
    ( ( k9_setfam_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('48',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( v2_waybel_0 @ X35 @ ( k3_yellow_1 @ ( k2_struct_0 @ X36 ) ) )
      | ~ ( v13_waybel_0 @ X35 @ ( k3_yellow_1 @ ( k2_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X36 ) ) ) )
      | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X36 ) ) @ X35 @ ( k9_setfam_1 @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X36 @ ( k3_yellow19 @ X36 @ ( k2_struct_0 @ X36 ) @ X35 ) ) )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_2 @ ( k9_setfam_1 @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('53',plain,(
    ! [X30: $i] :
      ( ( k9_setfam_1 @ X30 )
      = ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('54',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k9_setfam_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_2 @ X0 )
      = ( k4_xboole_0 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k9_setfam_1 @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['49','50','55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k9_setfam_1 @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_B_2 @ ( k9_setfam_1 @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    sk_B_2
 != ( k4_xboole_0 @ sk_B_2 @ ( k9_setfam_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('70',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PRg7GBw3wJ
% 0.15/0.37  % Computer   : n015.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 11:41:53 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 154 iterations in 0.064s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.23/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.54  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.23/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.23/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.54  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.23/0.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.23/0.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.23/0.54  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.23/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.23/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.54  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.23/0.54  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.23/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.54  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.23/0.54  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.23/0.54  thf(t15_yellow19, conjecture,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.54             ( v1_subset_1 @
% 0.23/0.54               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.23/0.54             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.54             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.54             ( m1_subset_1 @
% 0.23/0.54               B @ 
% 0.23/0.54               ( k1_zfmisc_1 @
% 0.23/0.54                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.23/0.54           ( ( B ) =
% 0.23/0.54             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i]:
% 0.23/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.54          ( ![B:$i]:
% 0.23/0.54            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.54                ( v1_subset_1 @
% 0.23/0.54                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.23/0.54                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.54                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.54                ( m1_subset_1 @
% 0.23/0.54                  B @ 
% 0.23/0.54                  ( k1_zfmisc_1 @
% 0.23/0.54                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.23/0.54              ( ( B ) =
% 0.23/0.54                ( k2_yellow19 @
% 0.23/0.54                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.23/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(d3_struct_0, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.23/0.54  thf('1', plain,
% 0.23/0.54      (![X31 : $i]:
% 0.23/0.54         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.23/0.54  thf(t1_zfmisc_1, axiom,
% 0.23/0.54    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.23/0.54  thf('2', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.23/0.54      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.23/0.54  thf(redefinition_k9_setfam_1, axiom,
% 0.23/0.54    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.54  thf('3', plain, (![X30 : $i]: ((k9_setfam_1 @ X30) = (k1_zfmisc_1 @ X30))),
% 0.23/0.54      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.23/0.54  thf('4', plain, (((k9_setfam_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.23/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.54  thf(l27_zfmisc_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.23/0.54  thf('5', plain,
% 0.23/0.54      (![X18 : $i, X19 : $i]:
% 0.23/0.54         ((r1_xboole_0 @ (k1_tarski @ X18) @ X19) | (r2_hidden @ X18 @ X19))),
% 0.23/0.54      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_xboole_0 @ (k9_setfam_1 @ k1_xboole_0) @ X0)
% 0.23/0.54          | (r2_hidden @ k1_xboole_0 @ X0))),
% 0.23/0.54      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.54  thf(t34_mcart_1, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.54          ( ![B:$i]:
% 0.23/0.54            ( ~( ( r2_hidden @ B @ A ) & 
% 0.23/0.54                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.23/0.54                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.23/0.54                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      (![X25 : $i]:
% 0.23/0.54         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X25) @ X25))),
% 0.23/0.54      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.23/0.54  thf(t4_xboole_0, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.23/0.54          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.23/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r2_hidden @ k1_xboole_0 @ X0)
% 0.23/0.54          | ((k3_xboole_0 @ (k9_setfam_1 @ k1_xboole_0) @ X0) = (k1_xboole_0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['6', '9'])).
% 0.23/0.54  thf(commutativity_k2_tarski, axiom,
% 0.23/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      (![X10 : $i, X11 : $i]:
% 0.23/0.54         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.23/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.23/0.54  thf(t12_setfam_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (![X23 : $i, X24 : $i]:
% 0.23/0.54         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 0.23/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (![X23 : $i, X24 : $i]:
% 0.23/0.54         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 0.23/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.23/0.54  thf('15', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.23/0.54  thf(t100_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (![X7 : $i, X8 : $i]:
% 0.23/0.54         ((k4_xboole_0 @ X7 @ X8)
% 0.23/0.54           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.54  thf('17', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.23/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.23/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('18', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((k4_xboole_0 @ X0 @ (k9_setfam_1 @ k1_xboole_0))
% 0.23/0.54            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.23/0.54          | (r2_hidden @ k1_xboole_0 @ X0))),
% 0.23/0.54      inference('sup+', [status(thm)], ['10', '17'])).
% 0.23/0.54  thf(t5_boole, axiom,
% 0.23/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.54  thf('19', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.23/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.23/0.54  thf('20', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((k4_xboole_0 @ X0 @ (k9_setfam_1 @ k1_xboole_0)) = (X0))
% 0.23/0.54          | (r2_hidden @ k1_xboole_0 @ X0))),
% 0.23/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B_2 @ 
% 0.23/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('22', plain, (![X30 : $i]: ((k9_setfam_1 @ X30) = (k1_zfmisc_1 @ X30))),
% 0.23/0.54      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.23/0.54  thf('23', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B_2 @ 
% 0.23/0.54        (k9_setfam_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.23/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.23/0.54  thf(t4_waybel_7, axiom,
% 0.23/0.54    (![A:$i]: ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) = ( k9_setfam_1 @ A ) ))).
% 0.23/0.54  thf('24', plain,
% 0.23/0.54      (![X34 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X34)) = (k9_setfam_1 @ X34))),
% 0.23/0.54      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.23/0.54  thf('25', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B_2 @ 
% 0.23/0.54        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.23/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.54  thf(t2_yellow19, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.54             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.23/0.54             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.23/0.54             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.23/0.54             ( m1_subset_1 @
% 0.23/0.54               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.23/0.54           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.23/0.54  thf('26', plain,
% 0.23/0.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ X37)
% 0.23/0.54          | ~ (v1_subset_1 @ X37 @ (u1_struct_0 @ (k3_yellow_1 @ X38)))
% 0.23/0.54          | ~ (v2_waybel_0 @ X37 @ (k3_yellow_1 @ X38))
% 0.23/0.54          | ~ (v13_waybel_0 @ X37 @ (k3_yellow_1 @ X38))
% 0.23/0.54          | ~ (m1_subset_1 @ X37 @ 
% 0.23/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X38))))
% 0.23/0.54          | ~ (r2_hidden @ X39 @ X37)
% 0.23/0.54          | ~ (v1_xboole_0 @ X39)
% 0.23/0.54          | (v1_xboole_0 @ X38))),
% 0.23/0.54      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      (![X34 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X34)) = (k9_setfam_1 @ X34))),
% 0.23/0.54      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.23/0.54  thf('28', plain,
% 0.23/0.54      (![X34 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X34)) = (k9_setfam_1 @ X34))),
% 0.23/0.54      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.23/0.54  thf('29', plain, (![X30 : $i]: ((k9_setfam_1 @ X30) = (k1_zfmisc_1 @ X30))),
% 0.23/0.54      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.23/0.54  thf('30', plain,
% 0.23/0.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ X37)
% 0.23/0.54          | ~ (v1_subset_1 @ X37 @ (k9_setfam_1 @ X38))
% 0.23/0.54          | ~ (v2_waybel_0 @ X37 @ (k3_yellow_1 @ X38))
% 0.23/0.54          | ~ (v13_waybel_0 @ X37 @ (k3_yellow_1 @ X38))
% 0.23/0.54          | ~ (m1_subset_1 @ X37 @ (k9_setfam_1 @ (k9_setfam_1 @ X38)))
% 0.23/0.54          | ~ (r2_hidden @ X39 @ X37)
% 0.23/0.54          | ~ (v1_xboole_0 @ X39)
% 0.23/0.54          | (v1_xboole_0 @ X38))),
% 0.23/0.54      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.23/0.54  thf('31', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.23/0.54          | ~ (v1_xboole_0 @ X0)
% 0.23/0.54          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.23/0.54          | ~ (v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.23/0.54          | ~ (v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.23/0.54          | ~ (v1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)))
% 0.23/0.54          | (v1_xboole_0 @ sk_B_2))),
% 0.23/0.54      inference('sup-', [status(thm)], ['25', '30'])).
% 0.23/0.54  thf('32', plain,
% 0.23/0.54      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('33', plain,
% 0.23/0.54      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('34', plain,
% 0.23/0.54      ((v1_subset_1 @ sk_B_2 @ 
% 0.23/0.54        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('35', plain,
% 0.23/0.54      (![X34 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X34)) = (k9_setfam_1 @ X34))),
% 0.23/0.54      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.23/0.54  thf('36', plain,
% 0.23/0.54      ((v1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.23/0.54  thf('37', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.23/0.54          | ~ (v1_xboole_0 @ X0)
% 0.23/0.54          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.23/0.54          | (v1_xboole_0 @ sk_B_2))),
% 0.23/0.54      inference('demod', [status(thm)], ['31', '32', '33', '36'])).
% 0.23/0.54  thf('38', plain,
% 0.23/0.54      ((((k4_xboole_0 @ sk_B_2 @ (k9_setfam_1 @ k1_xboole_0)) = (sk_B_2))
% 0.23/0.54        | (v1_xboole_0 @ sk_B_2)
% 0.23/0.54        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.23/0.54        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['20', '37'])).
% 0.23/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.23/0.54  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.54  thf('40', plain,
% 0.23/0.54      ((((k4_xboole_0 @ sk_B_2 @ (k9_setfam_1 @ k1_xboole_0)) = (sk_B_2))
% 0.23/0.54        | (v1_xboole_0 @ sk_B_2)
% 0.23/0.54        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.23/0.54  thf('41', plain,
% 0.23/0.54      (((sk_B_2)
% 0.23/0.54         != (k2_yellow19 @ sk_A @ 
% 0.23/0.54             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('42', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B_2 @ 
% 0.23/0.54        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.23/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.54  thf(t14_yellow19, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.54             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.54             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.54             ( m1_subset_1 @
% 0.23/0.54               B @ 
% 0.23/0.54               ( k1_zfmisc_1 @
% 0.23/0.54                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.23/0.54           ( ( k7_subset_1 @
% 0.23/0.54               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.23/0.54               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.23/0.54             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.23/0.54  thf('43', plain,
% 0.23/0.54      (![X35 : $i, X36 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ X35)
% 0.23/0.54          | ~ (v2_waybel_0 @ X35 @ (k3_yellow_1 @ (k2_struct_0 @ X36)))
% 0.23/0.54          | ~ (v13_waybel_0 @ X35 @ (k3_yellow_1 @ (k2_struct_0 @ X36)))
% 0.23/0.54          | ~ (m1_subset_1 @ X35 @ 
% 0.23/0.54               (k1_zfmisc_1 @ 
% 0.23/0.54                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X36)))))
% 0.23/0.54          | ((k7_subset_1 @ 
% 0.23/0.54              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X36))) @ X35 @ 
% 0.23/0.54              (k1_tarski @ k1_xboole_0))
% 0.23/0.54              = (k2_yellow19 @ X36 @ 
% 0.23/0.54                 (k3_yellow19 @ X36 @ (k2_struct_0 @ X36) @ X35)))
% 0.23/0.54          | ~ (l1_struct_0 @ X36)
% 0.23/0.54          | (v2_struct_0 @ X36))),
% 0.23/0.54      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.23/0.54  thf('44', plain,
% 0.23/0.54      (![X34 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X34)) = (k9_setfam_1 @ X34))),
% 0.23/0.54      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.23/0.54  thf('45', plain, (![X30 : $i]: ((k9_setfam_1 @ X30) = (k1_zfmisc_1 @ X30))),
% 0.23/0.54      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.23/0.54  thf('46', plain,
% 0.23/0.54      (![X34 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X34)) = (k9_setfam_1 @ X34))),
% 0.23/0.54      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.23/0.54  thf('47', plain, (((k9_setfam_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.23/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.54  thf('48', plain,
% 0.23/0.54      (![X35 : $i, X36 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ X35)
% 0.23/0.54          | ~ (v2_waybel_0 @ X35 @ (k3_yellow_1 @ (k2_struct_0 @ X36)))
% 0.23/0.54          | ~ (v13_waybel_0 @ X35 @ (k3_yellow_1 @ (k2_struct_0 @ X36)))
% 0.23/0.54          | ~ (m1_subset_1 @ X35 @ 
% 0.23/0.54               (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ X36))))
% 0.23/0.54          | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ X36)) @ X35 @ 
% 0.23/0.54              (k9_setfam_1 @ k1_xboole_0))
% 0.23/0.54              = (k2_yellow19 @ X36 @ 
% 0.23/0.54                 (k3_yellow19 @ X36 @ (k2_struct_0 @ X36) @ X35)))
% 0.23/0.54          | ~ (l1_struct_0 @ X36)
% 0.23/0.54          | (v2_struct_0 @ X36))),
% 0.23/0.54      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.23/0.54  thf('49', plain,
% 0.23/0.54      (((v2_struct_0 @ sk_A)
% 0.23/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.23/0.54        | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_2 @ 
% 0.23/0.54            (k9_setfam_1 @ k1_xboole_0))
% 0.23/0.54            = (k2_yellow19 @ sk_A @ 
% 0.23/0.54               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.23/0.54        | ~ (v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.23/0.54        | ~ (v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.23/0.54        | (v1_xboole_0 @ sk_B_2))),
% 0.23/0.54      inference('sup-', [status(thm)], ['42', '48'])).
% 0.23/0.54  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('51', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B_2 @ 
% 0.23/0.54        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.23/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.23/0.54  thf('52', plain,
% 0.23/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.23/0.54          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.23/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.23/0.54  thf('53', plain, (![X30 : $i]: ((k9_setfam_1 @ X30) = (k1_zfmisc_1 @ X30))),
% 0.23/0.54      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.23/0.54  thf('54', plain,
% 0.23/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X20 @ (k9_setfam_1 @ X21))
% 0.23/0.54          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.23/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.23/0.54  thf('55', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_2 @ X0)
% 0.23/0.54           = (k4_xboole_0 @ sk_B_2 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['51', '54'])).
% 0.23/0.54  thf('56', plain,
% 0.23/0.54      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('57', plain,
% 0.23/0.54      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('58', plain,
% 0.23/0.54      (((v2_struct_0 @ sk_A)
% 0.23/0.54        | ((k4_xboole_0 @ sk_B_2 @ (k9_setfam_1 @ k1_xboole_0))
% 0.23/0.54            = (k2_yellow19 @ sk_A @ 
% 0.23/0.54               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.23/0.54        | (v1_xboole_0 @ sk_B_2))),
% 0.23/0.54      inference('demod', [status(thm)], ['49', '50', '55', '56', '57'])).
% 0.23/0.54  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('60', plain,
% 0.23/0.54      (((v1_xboole_0 @ sk_B_2)
% 0.23/0.54        | ((k4_xboole_0 @ sk_B_2 @ (k9_setfam_1 @ k1_xboole_0))
% 0.23/0.54            = (k2_yellow19 @ sk_A @ 
% 0.23/0.54               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.23/0.54      inference('clc', [status(thm)], ['58', '59'])).
% 0.23/0.54  thf('61', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('62', plain,
% 0.23/0.54      (((k4_xboole_0 @ sk_B_2 @ (k9_setfam_1 @ k1_xboole_0))
% 0.23/0.54         = (k2_yellow19 @ sk_A @ 
% 0.23/0.54            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.23/0.54      inference('clc', [status(thm)], ['60', '61'])).
% 0.23/0.54  thf('63', plain,
% 0.23/0.54      (((sk_B_2) != (k4_xboole_0 @ sk_B_2 @ (k9_setfam_1 @ k1_xboole_0)))),
% 0.23/0.54      inference('demod', [status(thm)], ['41', '62'])).
% 0.23/0.54  thf('64', plain,
% 0.23/0.54      (((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['40', '63'])).
% 0.23/0.55  thf('65', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('66', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.23/0.55      inference('clc', [status(thm)], ['64', '65'])).
% 0.23/0.55  thf('67', plain,
% 0.23/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.55      inference('sup+', [status(thm)], ['1', '66'])).
% 0.23/0.55  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('69', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['67', '68'])).
% 0.23/0.55  thf(fc2_struct_0, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.55  thf('70', plain,
% 0.23/0.55      (![X32 : $i]:
% 0.23/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.23/0.55          | ~ (l1_struct_0 @ X32)
% 0.23/0.55          | (v2_struct_0 @ X32))),
% 0.23/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.23/0.55  thf('71', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.23/0.55  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('73', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.55      inference('demod', [status(thm)], ['71', '72'])).
% 0.23/0.55  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 0.23/0.55  
% 0.23/0.55  % SZS output end Refutation
% 0.23/0.55  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
