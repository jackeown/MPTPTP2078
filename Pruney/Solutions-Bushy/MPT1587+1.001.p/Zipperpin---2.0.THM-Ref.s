%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1587+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GRvteqXUwn

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 128 expanded)
%              Number of leaves         :   21 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  704 (3804 expanded)
%              Number of equality atoms :   15 (  66 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(k7_domain_1_type,type,(
    k7_domain_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_yellow_0_type,type,(
    v4_yellow_0: $i > $i > $o )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(t66_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_yellow_0 @ B @ A )
            & ( m1_yellow_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ( ( ( r2_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ B ) @ C @ D ) )
                      & ( r2_hidden @ ( k2_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ B ) @ C @ D ) ) @ ( u1_struct_0 @ B ) ) )
                   => ( ( r2_yellow_0 @ B @ ( k7_domain_1 @ ( u1_struct_0 @ B ) @ C @ D ) )
                      & ( ( k2_yellow_0 @ B @ ( k7_domain_1 @ ( u1_struct_0 @ B ) @ C @ D ) )
                        = ( k2_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_yellow_0 @ B @ A )
              & ( m1_yellow_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ( ( ( r2_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ B ) @ C @ D ) )
                        & ( r2_hidden @ ( k2_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ B ) @ C @ D ) ) @ ( u1_struct_0 @ B ) ) )
                     => ( ( r2_yellow_0 @ B @ ( k7_domain_1 @ ( u1_struct_0 @ B ) @ C @ D ) )
                        & ( ( k2_yellow_0 @ B @ ( k7_domain_1 @ ( u1_struct_0 @ B ) @ C @ D ) )
                          = ( k2_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_yellow_0])).

thf('0',plain,
    ( ~ ( r2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
    | ( ( k2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
     != ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
   <= ~ ( r2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_yellow_0,axiom,(
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
             => ( ( ( r2_yellow_0 @ A @ C )
                  & ( r2_hidden @ ( k2_yellow_0 @ A @ C ) @ ( u1_struct_0 @ B ) ) )
               => ( ( r2_yellow_0 @ B @ C )
                  & ( ( k2_yellow_0 @ B @ C )
                    = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v4_yellow_0 @ X3 @ X4 )
      | ~ ( m1_yellow_0 @ X3 @ X4 )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ( ( k2_yellow_0 @ X3 @ X5 )
        = ( k2_yellow_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_yellow_0])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( k2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
      = ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
    | ~ ( m1_yellow_0 @ sk_B @ sk_A )
    | ~ ( v4_yellow_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( m1_subset_1 @ ( k7_domain_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ X1 )
      | ( m1_subset_1 @ ( k7_domain_1 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    r2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
      = ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
      = ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
    = ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
     != ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) )
   <= ( ( k2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
     != ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
     != ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) )
   <= ( ( k2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
     != ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
    = ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( r2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
    | ( ( k2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
     != ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,(
    ~ ( r2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,(
    r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v4_yellow_0 @ X3 @ X4 )
      | ~ ( m1_yellow_0 @ X3 @ X4 )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_yellow_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
    | ~ ( m1_yellow_0 @ sk_B @ sk_A )
    | ~ ( v4_yellow_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('36',plain,(
    r2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v4_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r2_yellow_0 @ sk_B @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['29','43'])).


%------------------------------------------------------------------------------
