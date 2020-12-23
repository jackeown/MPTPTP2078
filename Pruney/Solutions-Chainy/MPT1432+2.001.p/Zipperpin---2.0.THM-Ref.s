%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xy9QMpmJh6

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:21 EST 2020

% Result     : Theorem 3.13s
% Output     : Refutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  276 ( 905 expanded)
%              Number of leaves         :   23 ( 262 expanded)
%              Depth                    :   19
%              Number of atoms          : 4771 (35875 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_binop_1_type,type,(
    r2_binop_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_domain_1_type,type,(
    k1_domain_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_filter_1_type,type,(
    k6_filter_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_binop_1_type,type,(
    r1_binop_1: $i > $i > $i > $o )).

thf(r3_binop_1_type,type,(
    r3_binop_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t27_filter_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ B )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( k2_zfmisc_1 @ A @ A ) @ A )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( k2_zfmisc_1 @ B @ B ) @ B )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) )
                         => ( ( ( r3_binop_1 @ A @ C @ E )
                              & ( r3_binop_1 @ B @ D @ F ) )
                          <=> ( r3_binop_1 @ ( k2_zfmisc_1 @ A @ B ) @ ( k1_domain_1 @ A @ B @ C @ D ) @ ( k6_filter_1 @ A @ B @ E @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ B )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( k2_zfmisc_1 @ A @ A ) @ A )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( k2_zfmisc_1 @ B @ B ) @ B )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) )
                           => ( ( ( r3_binop_1 @ A @ C @ E )
                                & ( r3_binop_1 @ B @ D @ F ) )
                            <=> ( r3_binop_1 @ ( k2_zfmisc_1 @ A @ B ) @ ( k1_domain_1 @ A @ B @ C @ D ) @ ( k6_filter_1 @ A @ B @ E @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_filter_1])).

thf('0',plain,
    ( ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
    | ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r3_binop_1 @ sk_B @ sk_D @ sk_F )
    | ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
    | ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_filter_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k2_zfmisc_1 @ B @ B ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k6_filter_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k6_filter_1 @ A @ B @ C @ D ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ B ) ) @ ( k2_zfmisc_1 @ A @ B ) )
        & ( m1_subset_1 @ ( k6_filter_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ B ) ) @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 ) ) )
      | ( m1_subset_1 @ ( k6_filter_1 @ X8 @ X10 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_filter_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k6_filter_1 @ sk_A @ X0 @ sk_E @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k6_filter_1 @ sk_A @ X0 @ sk_E @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
    | ( m1_subset_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(d7_binop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
         => ( ( r3_binop_1 @ A @ B @ C )
          <=> ( ( r1_binop_1 @ A @ B @ C )
              & ( r2_binop_1 @ A @ B @ C ) ) ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r3_binop_1 @ X5 @ X6 @ X4 )
      | ( r2_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 ) ) )
      | ( v1_funct_2 @ ( k6_filter_1 @ X8 @ X10 @ X7 @ X9 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_filter_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k6_filter_1 @ sk_A @ X0 @ sk_E @ X1 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k6_filter_1 @ sk_A @ X0 @ sk_E @ X1 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
    | ( v1_funct_2 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( v1_funct_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 ) ) )
      | ( v1_funct_1 @ ( k6_filter_1 @ X8 @ X10 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_filter_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k6_filter_1 @ sk_A @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k6_filter_1 @ sk_A @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
    | ( v1_funct_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['28','39'])).

thf('41',plain,
    ( ( ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( m1_subset_1 @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['3','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ C @ A )
        & ( m1_subset_1 @ D @ B ) )
     => ( m1_subset_1 @ ( k1_domain_1 @ A @ B @ C @ D ) @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ X2 )
      | ( m1_subset_1 @ ( k1_domain_1 @ X1 @ X2 @ X0 @ X3 ) @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_domain_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_domain_1 @ sk_A @ X0 @ sk_C @ X1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['41','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ B )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( k2_zfmisc_1 @ A @ A ) @ A )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( k2_zfmisc_1 @ B @ B ) @ B )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) )
                         => ( ( ( r2_binop_1 @ A @ C @ E )
                              & ( r2_binop_1 @ B @ D @ F ) )
                          <=> ( r2_binop_1 @ ( k2_zfmisc_1 @ A @ B ) @ ( k1_domain_1 @ A @ B @ C @ D ) @ ( k6_filter_1 @ A @ B @ E @ F ) ) ) ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ ( k2_zfmisc_1 @ X17 @ X17 ) @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) @ X17 ) ) )
      | ~ ( r2_binop_1 @ ( k2_zfmisc_1 @ X20 @ X17 ) @ ( k1_domain_1 @ X20 @ X17 @ X21 @ X18 ) @ ( k6_filter_1 @ X20 @ X17 @ X22 @ X19 ) )
      | ( r2_binop_1 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t26_filter_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r2_binop_1 @ sk_B @ X3 @ sk_F )
      | ~ ( r2_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r2_binop_1 @ sk_B @ X3 @ sk_F )
      | ~ ( r2_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_D @ sk_B )
      | ( r2_binop_1 @ sk_B @ sk_D @ sk_F )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_subset_1 @ sk_C @ sk_A )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_binop_1 @ sk_B @ sk_D @ sk_F )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r2_binop_1 @ sk_B @ sk_D @ sk_F ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r2_binop_1 @ sk_B @ sk_D @ sk_F )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r1_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( r2_binop_1 @ X5 @ X6 @ X4 )
      | ( r3_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( r3_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( r2_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( r1_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( r3_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( r2_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( r1_binop_1 @ sk_B @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( ~ ( r1_binop_1 @ sk_B @ sk_D @ sk_F )
      | ( r3_binop_1 @ sk_B @ sk_D @ sk_F )
      | ~ ( m1_subset_1 @ sk_D @ sk_B ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,
    ( ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['2'])).

thf('77',plain,(
    m1_subset_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('78',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r3_binop_1 @ X5 @ X6 @ X4 )
      | ( r1_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_2 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( v1_funct_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( m1_subset_1 @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    m1_subset_1 @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('86',plain,
    ( ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ B )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( k2_zfmisc_1 @ A @ A ) @ A )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( k2_zfmisc_1 @ B @ B ) @ B )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) )
                         => ( ( ( r1_binop_1 @ A @ C @ E )
                              & ( r1_binop_1 @ B @ D @ F ) )
                          <=> ( r1_binop_1 @ ( k2_zfmisc_1 @ A @ B ) @ ( k1_domain_1 @ A @ B @ C @ D ) @ ( k6_filter_1 @ A @ B @ E @ F ) ) ) ) ) ) ) ) ) )).

thf('88',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 ) ) )
      | ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ X14 @ X11 ) @ ( k1_domain_1 @ X14 @ X11 @ X15 @ X12 ) @ ( k6_filter_1 @ X14 @ X11 @ X16 @ X13 ) )
      | ( r1_binop_1 @ X11 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_filter_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r1_binop_1 @ sk_B @ X3 @ sk_F )
      | ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r1_binop_1 @ sk_B @ X3 @ sk_F )
      | ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_D @ sk_B )
      | ( r1_binop_1 @ sk_B @ sk_D @ sk_F )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_subset_1 @ sk_C @ sk_A )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r1_binop_1 @ sk_B @ sk_D @ sk_F )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97','98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r1_binop_1 @ sk_B @ sk_D @ sk_F ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( r1_binop_1 @ sk_B @ sk_D @ sk_F )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( r3_binop_1 @ sk_B @ sk_D @ sk_F )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['75','103','104'])).

thf('106',plain,
    ( ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
    | ~ ( r3_binop_1 @ sk_B @ sk_D @ sk_F )
    | ~ ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ~ ( r3_binop_1 @ sk_B @ sk_D @ sk_F )
   <= ~ ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference(split,[status(esa)],['106'])).

thf('108',plain,
    ( ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
    | ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,
    ( ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['41','50'])).

thf('110',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ ( k2_zfmisc_1 @ X17 @ X17 ) @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) @ X17 ) ) )
      | ~ ( r2_binop_1 @ ( k2_zfmisc_1 @ X20 @ X17 ) @ ( k1_domain_1 @ X20 @ X17 @ X21 @ X18 ) @ ( k6_filter_1 @ X20 @ X17 @ X22 @ X19 ) )
      | ( r2_binop_1 @ X20 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t26_filter_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r2_binop_1 @ X0 @ X1 @ X2 )
      | ~ ( r2_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r2_binop_1 @ X0 @ X1 @ X2 )
      | ~ ( r2_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_D @ sk_B )
      | ( r2_binop_1 @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_subset_1 @ sk_C @ sk_A )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['109','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_binop_1 @ sk_A @ sk_C @ sk_E )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ sk_C @ sk_E ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( r2_binop_1 @ sk_A @ sk_C @ sk_E )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r1_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( r2_binop_1 @ X5 @ X6 @ X4 )
      | ( r3_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( ~ ( r1_binop_1 @ sk_A @ sk_C @ sk_E )
      | ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_subset_1 @ sk_C @ sk_A ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,
    ( ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('135',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 ) ) )
      | ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ X14 @ X11 ) @ ( k1_domain_1 @ X14 @ X11 @ X15 @ X12 ) @ ( k6_filter_1 @ X14 @ X11 @ X16 @ X13 ) )
      | ( r1_binop_1 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_filter_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r1_binop_1 @ X0 @ X1 @ X2 )
      | ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r1_binop_1 @ X0 @ X1 @ X2 )
      | ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_D @ sk_B )
      | ( r1_binop_1 @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_subset_1 @ sk_C @ sk_A )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['134','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r1_binop_1 @ sk_A @ sk_C @ sk_E )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['141','142','143','144','145','146'])).

thf('148',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ sk_C @ sk_E ) )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( r1_binop_1 @ sk_A @ sk_C @ sk_E )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
   <= ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['133','151','152'])).

thf('154',plain,
    ( ~ ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
   <= ~ ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['106'])).

thf('155',plain,
    ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
    | ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
    | ~ ( r3_binop_1 @ sk_B @ sk_D @ sk_F )
    | ~ ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['106'])).

thf('157',plain,
    ( ( r3_binop_1 @ sk_B @ sk_D @ sk_F )
   <= ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('158',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r3_binop_1 @ X5 @ X6 @ X4 )
      | ( r2_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( r2_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( r3_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( r2_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( r3_binop_1 @ sk_B @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ( ( r2_binop_1 @ sk_B @ sk_D @ sk_F )
      | ~ ( m1_subset_1 @ sk_D @ sk_B ) )
   <= ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['157','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( r2_binop_1 @ sk_B @ sk_D @ sk_F )
   <= ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['2'])).

thf('168',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r3_binop_1 @ X5 @ X6 @ X4 )
      | ( r2_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( ( r2_binop_1 @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_subset_1 @ sk_C @ sk_A ) )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['167','173'])).

thf('175',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( r2_binop_1 @ sk_A @ sk_C @ sk_E )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ ( k2_zfmisc_1 @ X17 @ X17 ) @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) @ X17 ) ) )
      | ~ ( r2_binop_1 @ X20 @ X21 @ X22 )
      | ~ ( r2_binop_1 @ X17 @ X18 @ X19 )
      | ( r2_binop_1 @ ( k2_zfmisc_1 @ X20 @ X17 ) @ ( k1_domain_1 @ X20 @ X17 @ X21 @ X18 ) @ ( k6_filter_1 @ X20 @ X17 @ X22 @ X19 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t26_filter_1])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r2_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( r2_binop_1 @ sk_B @ X3 @ sk_F )
      | ~ ( r2_binop_1 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r2_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( r2_binop_1 @ sk_B @ X3 @ sk_F )
      | ~ ( r2_binop_1 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_binop_1 @ sk_A @ X1 @ sk_E )
      | ~ ( r2_binop_1 @ sk_B @ X0 @ sk_F )
      | ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ X1 @ X0 ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['177','183'])).

thf('185',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_binop_1 @ sk_A @ X1 @ sk_E )
      | ~ ( r2_binop_1 @ sk_B @ X0 @ sk_F )
      | ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ X1 @ X0 ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ sk_A )
        | ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
        | ~ ( r2_binop_1 @ sk_B @ X0 @ sk_F )
        | ~ ( m1_subset_1 @ X0 @ sk_B )
        | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['176','187'])).

thf('189',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_A )
        | ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
        | ~ ( r2_binop_1 @ sk_B @ X0 @ sk_F )
        | ~ ( m1_subset_1 @ X0 @ sk_B )
        | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_D @ sk_B )
      | ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['166','190'])).

thf('192',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,(
    m1_subset_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('199',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r1_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( r2_binop_1 @ X5 @ X6 @ X4 )
      | ( r3_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    v1_funct_2 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('202',plain,(
    v1_funct_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ( ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( m1_subset_1 @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['197','203'])).

thf('205',plain,
    ( ( r3_binop_1 @ sk_B @ sk_D @ sk_F )
   <= ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('206',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r3_binop_1 @ X5 @ X6 @ X4 )
      | ( r1_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( r1_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( r3_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( r1_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( r3_binop_1 @ sk_B @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,
    ( ( ( r1_binop_1 @ sk_B @ sk_D @ sk_F )
      | ~ ( m1_subset_1 @ sk_D @ sk_B ) )
   <= ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['205','211'])).

thf('213',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( r1_binop_1 @ sk_B @ sk_D @ sk_F )
   <= ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['2'])).

thf('216',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r3_binop_1 @ X5 @ X6 @ X4 )
      | ( r1_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['218','219','220'])).

thf('222',plain,
    ( ( ( r1_binop_1 @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_subset_1 @ sk_C @ sk_A ) )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['215','221'])).

thf('223',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( r1_binop_1 @ sk_A @ sk_C @ sk_E )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 ) ) )
      | ~ ( r1_binop_1 @ X14 @ X15 @ X16 )
      | ~ ( r1_binop_1 @ X11 @ X12 @ X13 )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ X14 @ X11 ) @ ( k1_domain_1 @ X14 @ X11 @ X15 @ X12 ) @ ( k6_filter_1 @ X14 @ X11 @ X16 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_filter_1])).

thf('228',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( r1_binop_1 @ sk_B @ X3 @ sk_F )
      | ~ ( r1_binop_1 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X0 ) ) )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k1_domain_1 @ X0 @ sk_B @ X1 @ X3 ) @ ( k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F ) )
      | ~ ( r1_binop_1 @ sk_B @ X3 @ sk_F )
      | ~ ( r1_binop_1 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r1_binop_1 @ sk_A @ X1 @ sk_E )
      | ~ ( r1_binop_1 @ sk_B @ X0 @ sk_F )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ X1 @ X0 ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['225','231'])).

thf('233',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r1_binop_1 @ sk_A @ X1 @ sk_E )
      | ~ ( r1_binop_1 @ sk_B @ X0 @ sk_F )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ X1 @ X0 ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['232','233','234'])).

thf('236',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ sk_A )
        | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
        | ~ ( r1_binop_1 @ sk_B @ X0 @ sk_F )
        | ~ ( m1_subset_1 @ X0 @ sk_B )
        | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['224','235'])).

thf('237',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_A )
        | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
        | ~ ( r1_binop_1 @ sk_B @ X0 @ sk_F )
        | ~ ( m1_subset_1 @ X0 @ sk_B )
        | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_D @ sk_B )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['214','238'])).

thf('240',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['241','242'])).

thf('244',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['243','244'])).

thf('246',plain,(
    m1_subset_1 @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('247',plain,
    ( ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['204','245','246'])).

thf('248',plain,
    ( ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['106'])).

thf('249',plain,
    ( ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
    | ~ ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
    | ~ ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,
    ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
    | ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['2'])).

thf('251',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','108','155','156','249','250'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xy9QMpmJh6
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.13/3.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.13/3.35  % Solved by: fo/fo7.sh
% 3.13/3.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.13/3.35  % done 1203 iterations in 2.890s
% 3.13/3.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.13/3.35  % SZS output start Refutation
% 3.13/3.35  thf(r2_binop_1_type, type, r2_binop_1: $i > $i > $i > $o).
% 3.13/3.35  thf(sk_B_type, type, sk_B: $i).
% 3.13/3.35  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.13/3.35  thf(k1_domain_1_type, type, k1_domain_1: $i > $i > $i > $i > $i).
% 3.13/3.35  thf(sk_D_type, type, sk_D: $i).
% 3.13/3.35  thf(sk_F_type, type, sk_F: $i).
% 3.13/3.35  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.13/3.35  thf(k6_filter_1_type, type, k6_filter_1: $i > $i > $i > $i > $i).
% 3.13/3.35  thf(sk_E_type, type, sk_E: $i).
% 3.13/3.35  thf(sk_A_type, type, sk_A: $i).
% 3.13/3.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.13/3.35  thf(r1_binop_1_type, type, r1_binop_1: $i > $i > $i > $o).
% 3.13/3.35  thf(r3_binop_1_type, type, r3_binop_1: $i > $i > $i > $o).
% 3.13/3.35  thf(sk_C_type, type, sk_C: $i).
% 3.13/3.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.13/3.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.13/3.35  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.13/3.35  thf(t27_filter_1, conjecture,
% 3.13/3.35    (![A:$i]:
% 3.13/3.35     ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.13/3.35       ( ![B:$i]:
% 3.13/3.35         ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.13/3.35           ( ![C:$i]:
% 3.13/3.35             ( ( m1_subset_1 @ C @ A ) =>
% 3.13/3.35               ( ![D:$i]:
% 3.13/3.35                 ( ( m1_subset_1 @ D @ B ) =>
% 3.13/3.35                   ( ![E:$i]:
% 3.13/3.35                     ( ( ( v1_funct_1 @ E ) & 
% 3.13/3.35                         ( v1_funct_2 @ E @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 3.13/3.35                         ( m1_subset_1 @
% 3.13/3.35                           E @ 
% 3.13/3.35                           ( k1_zfmisc_1 @
% 3.13/3.35                             ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 3.13/3.35                       ( ![F:$i]:
% 3.13/3.35                         ( ( ( v1_funct_1 @ F ) & 
% 3.13/3.35                             ( v1_funct_2 @ F @ ( k2_zfmisc_1 @ B @ B ) @ B ) & 
% 3.13/3.35                             ( m1_subset_1 @
% 3.13/3.35                               F @ 
% 3.13/3.35                               ( k1_zfmisc_1 @
% 3.13/3.35                                 ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) ) =>
% 3.13/3.35                           ( ( ( r3_binop_1 @ A @ C @ E ) & 
% 3.13/3.35                               ( r3_binop_1 @ B @ D @ F ) ) <=>
% 3.13/3.35                             ( r3_binop_1 @
% 3.13/3.35                               ( k2_zfmisc_1 @ A @ B ) @ 
% 3.13/3.35                               ( k1_domain_1 @ A @ B @ C @ D ) @ 
% 3.13/3.35                               ( k6_filter_1 @ A @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.13/3.35  thf(zf_stmt_0, negated_conjecture,
% 3.13/3.35    (~( ![A:$i]:
% 3.13/3.35        ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.13/3.35          ( ![B:$i]:
% 3.13/3.35            ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.13/3.35              ( ![C:$i]:
% 3.13/3.35                ( ( m1_subset_1 @ C @ A ) =>
% 3.13/3.35                  ( ![D:$i]:
% 3.13/3.35                    ( ( m1_subset_1 @ D @ B ) =>
% 3.13/3.35                      ( ![E:$i]:
% 3.13/3.35                        ( ( ( v1_funct_1 @ E ) & 
% 3.13/3.35                            ( v1_funct_2 @ E @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 3.13/3.35                            ( m1_subset_1 @
% 3.13/3.35                              E @ 
% 3.13/3.35                              ( k1_zfmisc_1 @
% 3.13/3.35                                ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 3.13/3.35                          ( ![F:$i]:
% 3.13/3.35                            ( ( ( v1_funct_1 @ F ) & 
% 3.13/3.35                                ( v1_funct_2 @ F @ ( k2_zfmisc_1 @ B @ B ) @ B ) & 
% 3.13/3.35                                ( m1_subset_1 @
% 3.13/3.35                                  F @ 
% 3.13/3.35                                  ( k1_zfmisc_1 @
% 3.13/3.35                                    ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) ) =>
% 3.13/3.35                              ( ( ( r3_binop_1 @ A @ C @ E ) & 
% 3.13/3.35                                  ( r3_binop_1 @ B @ D @ F ) ) <=>
% 3.13/3.35                                ( r3_binop_1 @
% 3.13/3.35                                  ( k2_zfmisc_1 @ A @ B ) @ 
% 3.13/3.35                                  ( k1_domain_1 @ A @ B @ C @ D ) @ 
% 3.13/3.35                                  ( k6_filter_1 @ A @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 3.13/3.35    inference('cnf.neg', [status(esa)], [t27_filter_1])).
% 3.13/3.35  thf('0', plain,
% 3.13/3.35      (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35        | (r3_binop_1 @ sk_B @ sk_D @ sk_F))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('1', plain,
% 3.13/3.35      (((r3_binop_1 @ sk_B @ sk_D @ sk_F)) | 
% 3.13/3.35       ((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.35      inference('split', [status(esa)], ['0'])).
% 3.13/3.35  thf('2', plain,
% 3.13/3.35      (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35        | (r3_binop_1 @ sk_A @ sk_C @ sk_E))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('3', plain,
% 3.13/3.35      (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('split', [status(esa)], ['2'])).
% 3.13/3.35  thf('4', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_F @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('5', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_E @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf(dt_k6_filter_1, axiom,
% 3.13/3.35    (![A:$i,B:$i,C:$i,D:$i]:
% 3.13/3.35     ( ( ( v1_funct_1 @ C ) & 
% 3.13/3.35         ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 3.13/3.35         ( m1_subset_1 @
% 3.13/3.35           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) & 
% 3.13/3.35         ( v1_funct_1 @ D ) & 
% 3.13/3.35         ( v1_funct_2 @ D @ ( k2_zfmisc_1 @ B @ B ) @ B ) & 
% 3.13/3.35         ( m1_subset_1 @
% 3.13/3.35           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) ) =>
% 3.13/3.35       ( ( v1_funct_1 @ ( k6_filter_1 @ A @ B @ C @ D ) ) & 
% 3.13/3.35         ( v1_funct_2 @
% 3.13/3.35           ( k6_filter_1 @ A @ B @ C @ D ) @ 
% 3.13/3.35           ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ B ) ) @ 
% 3.13/3.35           ( k2_zfmisc_1 @ A @ B ) ) & 
% 3.13/3.35         ( m1_subset_1 @
% 3.13/3.35           ( k6_filter_1 @ A @ B @ C @ D ) @ 
% 3.13/3.35           ( k1_zfmisc_1 @
% 3.13/3.35             ( k2_zfmisc_1 @
% 3.13/3.35               ( k2_zfmisc_1 @
% 3.13/3.35                 ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ B ) ) @ 
% 3.13/3.35               ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 3.13/3.35  thf('6', plain,
% 3.13/3.35      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X7 @ 
% 3.13/3.35             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)))
% 3.13/3.35          | ~ (v1_funct_2 @ X7 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)
% 3.13/3.35          | ~ (v1_funct_1 @ X7)
% 3.13/3.35          | ~ (v1_funct_1 @ X9)
% 3.13/3.35          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)
% 3.13/3.35          | ~ (m1_subset_1 @ X9 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)))
% 3.13/3.35          | (m1_subset_1 @ (k6_filter_1 @ X8 @ X10 @ X7 @ X9) @ 
% 3.13/3.35             (k1_zfmisc_1 @ 
% 3.13/3.35              (k2_zfmisc_1 @ 
% 3.13/3.35               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10) @ 
% 3.13/3.35                (k2_zfmisc_1 @ X8 @ X10)) @ 
% 3.13/3.35               (k2_zfmisc_1 @ X8 @ X10)))))),
% 3.13/3.35      inference('cnf', [status(esa)], [dt_k6_filter_1])).
% 3.13/3.35  thf('7', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((m1_subset_1 @ (k6_filter_1 @ sk_A @ X0 @ sk_E @ X1) @ 
% 3.13/3.35           (k1_zfmisc_1 @ 
% 3.13/3.35            (k2_zfmisc_1 @ 
% 3.13/3.35             (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 3.13/3.35              (k2_zfmisc_1 @ sk_A @ X0)) @ 
% 3.13/3.35             (k2_zfmisc_1 @ sk_A @ X0))))
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.35          | ~ (v1_funct_2 @ X1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ X1)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_E)
% 3.13/3.35          | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A))),
% 3.13/3.35      inference('sup-', [status(thm)], ['5', '6'])).
% 3.13/3.35  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('9', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('10', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((m1_subset_1 @ (k6_filter_1 @ sk_A @ X0 @ sk_E @ X1) @ 
% 3.13/3.35           (k1_zfmisc_1 @ 
% 3.13/3.35            (k2_zfmisc_1 @ 
% 3.13/3.35             (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 3.13/3.35              (k2_zfmisc_1 @ sk_A @ X0)) @ 
% 3.13/3.35             (k2_zfmisc_1 @ sk_A @ X0))))
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.35          | ~ (v1_funct_2 @ X1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ X1))),
% 3.13/3.35      inference('demod', [status(thm)], ['7', '8', '9'])).
% 3.13/3.35  thf('11', plain,
% 3.13/3.35      ((~ (v1_funct_1 @ sk_F)
% 3.13/3.35        | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.35        | (m1_subset_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F) @ 
% 3.13/3.35           (k1_zfmisc_1 @ 
% 3.13/3.35            (k2_zfmisc_1 @ 
% 3.13/3.35             (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35              (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 3.13/3.35             (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['4', '10'])).
% 3.13/3.35  thf('12', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('13', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('14', plain,
% 3.13/3.35      ((m1_subset_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F) @ 
% 3.13/3.35        (k1_zfmisc_1 @ 
% 3.13/3.35         (k2_zfmisc_1 @ 
% 3.13/3.35          (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35           (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 3.13/3.35          (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 3.13/3.35      inference('demod', [status(thm)], ['11', '12', '13'])).
% 3.13/3.35  thf(d7_binop_1, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ( m1_subset_1 @ B @ A ) =>
% 3.13/3.35       ( ![C:$i]:
% 3.13/3.35         ( ( ( v1_funct_1 @ C ) & 
% 3.13/3.35             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 3.13/3.35             ( m1_subset_1 @
% 3.13/3.35               C @ 
% 3.13/3.35               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 3.13/3.35           ( ( r3_binop_1 @ A @ B @ C ) <=>
% 3.13/3.35             ( ( r1_binop_1 @ A @ B @ C ) & ( r2_binop_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.13/3.35  thf('15', plain,
% 3.13/3.35      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.13/3.35         (~ (v1_funct_1 @ X4)
% 3.13/3.35          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 3.13/3.35          | ~ (m1_subset_1 @ X4 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 3.13/3.35          | ~ (r3_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.35          | (r2_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.35          | ~ (m1_subset_1 @ X6 @ X5))),
% 3.13/3.35      inference('cnf', [status(esa)], [d7_binop_1])).
% 3.13/3.35  thf('16', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.35          | (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35          | ~ (r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35          | ~ (v1_funct_2 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F) @ 
% 3.13/3.35               (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35                (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 3.13/3.35               (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.35          | ~ (v1_funct_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['14', '15'])).
% 3.13/3.35  thf('17', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_F @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('18', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_E @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('19', plain,
% 3.13/3.35      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X7 @ 
% 3.13/3.35             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)))
% 3.13/3.35          | ~ (v1_funct_2 @ X7 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)
% 3.13/3.35          | ~ (v1_funct_1 @ X7)
% 3.13/3.35          | ~ (v1_funct_1 @ X9)
% 3.13/3.35          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)
% 3.13/3.35          | ~ (m1_subset_1 @ X9 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)))
% 3.13/3.35          | (v1_funct_2 @ (k6_filter_1 @ X8 @ X10 @ X7 @ X9) @ 
% 3.13/3.35             (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10) @ (k2_zfmisc_1 @ X8 @ X10)) @ 
% 3.13/3.35             (k2_zfmisc_1 @ X8 @ X10)))),
% 3.13/3.35      inference('cnf', [status(esa)], [dt_k6_filter_1])).
% 3.13/3.35  thf('20', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((v1_funct_2 @ (k6_filter_1 @ sk_A @ X0 @ sk_E @ X1) @ 
% 3.13/3.35           (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0) @ (k2_zfmisc_1 @ sk_A @ X0)) @ 
% 3.13/3.35           (k2_zfmisc_1 @ sk_A @ X0))
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.35          | ~ (v1_funct_2 @ X1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ X1)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_E)
% 3.13/3.35          | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A))),
% 3.13/3.35      inference('sup-', [status(thm)], ['18', '19'])).
% 3.13/3.35  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('22', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('23', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((v1_funct_2 @ (k6_filter_1 @ sk_A @ X0 @ sk_E @ X1) @ 
% 3.13/3.35           (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0) @ (k2_zfmisc_1 @ sk_A @ X0)) @ 
% 3.13/3.35           (k2_zfmisc_1 @ sk_A @ X0))
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.35          | ~ (v1_funct_2 @ X1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ X1))),
% 3.13/3.35      inference('demod', [status(thm)], ['20', '21', '22'])).
% 3.13/3.35  thf('24', plain,
% 3.13/3.35      ((~ (v1_funct_1 @ sk_F)
% 3.13/3.35        | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.35        | (v1_funct_2 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F) @ 
% 3.13/3.35           (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35            (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 3.13/3.35           (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['17', '23'])).
% 3.13/3.35  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('26', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('27', plain,
% 3.13/3.35      ((v1_funct_2 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F) @ 
% 3.13/3.35        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 3.13/3.35        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.13/3.35      inference('demod', [status(thm)], ['24', '25', '26'])).
% 3.13/3.35  thf('28', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.35          | (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35          | ~ (r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35          | ~ (v1_funct_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.35      inference('demod', [status(thm)], ['16', '27'])).
% 3.13/3.35  thf('29', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_F @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('30', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_E @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('31', plain,
% 3.13/3.35      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X7 @ 
% 3.13/3.35             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)))
% 3.13/3.35          | ~ (v1_funct_2 @ X7 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)
% 3.13/3.35          | ~ (v1_funct_1 @ X7)
% 3.13/3.35          | ~ (v1_funct_1 @ X9)
% 3.13/3.35          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)
% 3.13/3.35          | ~ (m1_subset_1 @ X9 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)))
% 3.13/3.35          | (v1_funct_1 @ (k6_filter_1 @ X8 @ X10 @ X7 @ X9)))),
% 3.13/3.35      inference('cnf', [status(esa)], [dt_k6_filter_1])).
% 3.13/3.35  thf('32', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((v1_funct_1 @ (k6_filter_1 @ sk_A @ X1 @ sk_E @ X0))
% 3.13/3.35          | ~ (m1_subset_1 @ X0 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X1) @ X1)))
% 3.13/3.35          | ~ (v1_funct_2 @ X0 @ (k2_zfmisc_1 @ X1 @ X1) @ X1)
% 3.13/3.35          | ~ (v1_funct_1 @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_E)
% 3.13/3.35          | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A))),
% 3.13/3.35      inference('sup-', [status(thm)], ['30', '31'])).
% 3.13/3.35  thf('33', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('34', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('35', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((v1_funct_1 @ (k6_filter_1 @ sk_A @ X1 @ sk_E @ X0))
% 3.13/3.35          | ~ (m1_subset_1 @ X0 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X1) @ X1)))
% 3.13/3.35          | ~ (v1_funct_2 @ X0 @ (k2_zfmisc_1 @ X1 @ X1) @ X1)
% 3.13/3.35          | ~ (v1_funct_1 @ X0))),
% 3.13/3.35      inference('demod', [status(thm)], ['32', '33', '34'])).
% 3.13/3.35  thf('36', plain,
% 3.13/3.35      ((~ (v1_funct_1 @ sk_F)
% 3.13/3.35        | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.35        | (v1_funct_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['29', '35'])).
% 3.13/3.35  thf('37', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('38', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('39', plain, ((v1_funct_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))),
% 3.13/3.35      inference('demod', [status(thm)], ['36', '37', '38'])).
% 3.13/3.35  thf('40', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.35          | (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35          | ~ (r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.35      inference('demod', [status(thm)], ['28', '39'])).
% 3.13/3.35  thf('41', plain,
% 3.13/3.35      ((((r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35          (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35          (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35         | ~ (m1_subset_1 @ (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35              (k2_zfmisc_1 @ sk_A @ sk_B))))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['3', '40'])).
% 3.13/3.35  thf('42', plain, ((m1_subset_1 @ sk_D @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('43', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf(dt_k1_domain_1, axiom,
% 3.13/3.35    (![A:$i,B:$i,C:$i,D:$i]:
% 3.13/3.35     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 3.13/3.35         ( m1_subset_1 @ C @ A ) & ( m1_subset_1 @ D @ B ) ) =>
% 3.13/3.35       ( m1_subset_1 @
% 3.13/3.35         ( k1_domain_1 @ A @ B @ C @ D ) @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 3.13/3.35  thf('44', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ X1)
% 3.13/3.35          | (v1_xboole_0 @ X2)
% 3.13/3.35          | (v1_xboole_0 @ X1)
% 3.13/3.35          | ~ (m1_subset_1 @ X3 @ X2)
% 3.13/3.35          | (m1_subset_1 @ (k1_domain_1 @ X1 @ X2 @ X0 @ X3) @ 
% 3.13/3.35             (k2_zfmisc_1 @ X1 @ X2)))),
% 3.13/3.35      inference('cnf', [status(esa)], [dt_k1_domain_1])).
% 3.13/3.35  thf('45', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((m1_subset_1 @ (k1_domain_1 @ sk_A @ X0 @ sk_C @ X1) @ 
% 3.13/3.35           (k2_zfmisc_1 @ sk_A @ X0))
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.35          | (v1_xboole_0 @ sk_A)
% 3.13/3.35          | (v1_xboole_0 @ X0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['43', '44'])).
% 3.13/3.35  thf('46', plain,
% 3.13/3.35      (((v1_xboole_0 @ sk_B)
% 3.13/3.35        | (v1_xboole_0 @ sk_A)
% 3.13/3.35        | (m1_subset_1 @ (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35           (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['42', '45'])).
% 3.13/3.35  thf('47', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('48', plain,
% 3.13/3.35      (((m1_subset_1 @ (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35         (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.35        | (v1_xboole_0 @ sk_A))),
% 3.13/3.35      inference('clc', [status(thm)], ['46', '47'])).
% 3.13/3.35  thf('49', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('50', plain,
% 3.13/3.35      ((m1_subset_1 @ (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.13/3.35      inference('clc', [status(thm)], ['48', '49'])).
% 3.13/3.35  thf('51', plain,
% 3.13/3.35      (((r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('demod', [status(thm)], ['41', '50'])).
% 3.13/3.35  thf('52', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_F @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf(t26_filter_1, axiom,
% 3.13/3.35    (![A:$i]:
% 3.13/3.35     ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.13/3.35       ( ![B:$i]:
% 3.13/3.35         ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.13/3.35           ( ![C:$i]:
% 3.13/3.35             ( ( m1_subset_1 @ C @ A ) =>
% 3.13/3.35               ( ![D:$i]:
% 3.13/3.35                 ( ( m1_subset_1 @ D @ B ) =>
% 3.13/3.35                   ( ![E:$i]:
% 3.13/3.35                     ( ( ( v1_funct_1 @ E ) & 
% 3.13/3.35                         ( v1_funct_2 @ E @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 3.13/3.35                         ( m1_subset_1 @
% 3.13/3.35                           E @ 
% 3.13/3.35                           ( k1_zfmisc_1 @
% 3.13/3.35                             ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 3.13/3.35                       ( ![F:$i]:
% 3.13/3.35                         ( ( ( v1_funct_1 @ F ) & 
% 3.13/3.35                             ( v1_funct_2 @ F @ ( k2_zfmisc_1 @ B @ B ) @ B ) & 
% 3.13/3.35                             ( m1_subset_1 @
% 3.13/3.35                               F @ 
% 3.13/3.35                               ( k1_zfmisc_1 @
% 3.13/3.35                                 ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) ) =>
% 3.13/3.35                           ( ( ( r2_binop_1 @ A @ C @ E ) & 
% 3.13/3.35                               ( r2_binop_1 @ B @ D @ F ) ) <=>
% 3.13/3.35                             ( r2_binop_1 @
% 3.13/3.35                               ( k2_zfmisc_1 @ A @ B ) @ 
% 3.13/3.35                               ( k1_domain_1 @ A @ B @ C @ D ) @ 
% 3.13/3.35                               ( k6_filter_1 @ A @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.13/3.35  thf('53', plain,
% 3.13/3.35      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.13/3.35         ((v1_xboole_0 @ X17)
% 3.13/3.35          | ~ (m1_subset_1 @ X18 @ X17)
% 3.13/3.35          | ~ (v1_funct_1 @ X19)
% 3.13/3.35          | ~ (v1_funct_2 @ X19 @ (k2_zfmisc_1 @ X17 @ X17) @ X17)
% 3.13/3.35          | ~ (m1_subset_1 @ X19 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17) @ X17)))
% 3.13/3.35          | ~ (r2_binop_1 @ (k2_zfmisc_1 @ X20 @ X17) @ 
% 3.13/3.35               (k1_domain_1 @ X20 @ X17 @ X21 @ X18) @ 
% 3.13/3.35               (k6_filter_1 @ X20 @ X17 @ X22 @ X19))
% 3.13/3.35          | (r2_binop_1 @ X17 @ X18 @ X19)
% 3.13/3.35          | ~ (m1_subset_1 @ X22 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20) @ X20)))
% 3.13/3.35          | ~ (v1_funct_2 @ X22 @ (k2_zfmisc_1 @ X20 @ X20) @ X20)
% 3.13/3.35          | ~ (v1_funct_1 @ X22)
% 3.13/3.35          | ~ (m1_subset_1 @ X21 @ X20)
% 3.13/3.35          | (v1_xboole_0 @ X20))),
% 3.13/3.35      inference('cnf', [status(esa)], [t26_filter_1])).
% 3.13/3.35  thf('54', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.35         ((v1_xboole_0 @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ X2)
% 3.13/3.35          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.35          | (r2_binop_1 @ sk_B @ X3 @ sk_F)
% 3.13/3.35          | ~ (r2_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.35               (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.35          | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_F)
% 3.13/3.35          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.35          | (v1_xboole_0 @ sk_B))),
% 3.13/3.35      inference('sup-', [status(thm)], ['52', '53'])).
% 3.13/3.35  thf('55', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('56', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('57', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.35         ((v1_xboole_0 @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ X2)
% 3.13/3.35          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.35          | (r2_binop_1 @ sk_B @ X3 @ sk_F)
% 3.13/3.35          | ~ (r2_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.35               (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.35          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.35          | (v1_xboole_0 @ sk_B))),
% 3.13/3.35      inference('demod', [status(thm)], ['54', '55', '56'])).
% 3.13/3.35  thf('58', plain,
% 3.13/3.35      ((((v1_xboole_0 @ sk_B)
% 3.13/3.35         | ~ (m1_subset_1 @ sk_D @ sk_B)
% 3.13/3.35         | (r2_binop_1 @ sk_B @ sk_D @ sk_F)
% 3.13/3.35         | ~ (m1_subset_1 @ sk_E @ 
% 3.13/3.35              (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 3.13/3.35         | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 3.13/3.35         | ~ (v1_funct_1 @ sk_E)
% 3.13/3.35         | ~ (m1_subset_1 @ sk_C @ sk_A)
% 3.13/3.35         | (v1_xboole_0 @ sk_A)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['51', '57'])).
% 3.13/3.35  thf('59', plain, ((m1_subset_1 @ sk_D @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('60', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_E @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('61', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('62', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('63', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('64', plain,
% 3.13/3.35      ((((v1_xboole_0 @ sk_B)
% 3.13/3.35         | (r2_binop_1 @ sk_B @ sk_D @ sk_F)
% 3.13/3.35         | (v1_xboole_0 @ sk_A)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('demod', [status(thm)], ['58', '59', '60', '61', '62', '63'])).
% 3.13/3.35  thf('65', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('66', plain,
% 3.13/3.35      ((((v1_xboole_0 @ sk_A) | (r2_binop_1 @ sk_B @ sk_D @ sk_F)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('clc', [status(thm)], ['64', '65'])).
% 3.13/3.35  thf('67', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('68', plain,
% 3.13/3.35      (((r2_binop_1 @ sk_B @ sk_D @ sk_F))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('clc', [status(thm)], ['66', '67'])).
% 3.13/3.35  thf('69', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_F @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('70', plain,
% 3.13/3.35      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.13/3.35         (~ (v1_funct_1 @ X4)
% 3.13/3.35          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 3.13/3.35          | ~ (m1_subset_1 @ X4 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 3.13/3.35          | ~ (r1_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.35          | ~ (r2_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.35          | (r3_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.35          | ~ (m1_subset_1 @ X6 @ X5))),
% 3.13/3.35      inference('cnf', [status(esa)], [d7_binop_1])).
% 3.13/3.35  thf('71', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.35          | (r3_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.35          | ~ (r2_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.35          | ~ (r1_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.35          | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_F))),
% 3.13/3.35      inference('sup-', [status(thm)], ['69', '70'])).
% 3.13/3.35  thf('72', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('73', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('74', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.35          | (r3_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.35          | ~ (r2_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.35          | ~ (r1_binop_1 @ sk_B @ X0 @ sk_F))),
% 3.13/3.35      inference('demod', [status(thm)], ['71', '72', '73'])).
% 3.13/3.35  thf('75', plain,
% 3.13/3.35      (((~ (r1_binop_1 @ sk_B @ sk_D @ sk_F)
% 3.13/3.35         | (r3_binop_1 @ sk_B @ sk_D @ sk_F)
% 3.13/3.35         | ~ (m1_subset_1 @ sk_D @ sk_B)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['68', '74'])).
% 3.13/3.35  thf('76', plain,
% 3.13/3.35      (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('split', [status(esa)], ['2'])).
% 3.13/3.35  thf('77', plain,
% 3.13/3.35      ((m1_subset_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F) @ 
% 3.13/3.35        (k1_zfmisc_1 @ 
% 3.13/3.35         (k2_zfmisc_1 @ 
% 3.13/3.35          (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35           (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 3.13/3.35          (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 3.13/3.35      inference('demod', [status(thm)], ['11', '12', '13'])).
% 3.13/3.35  thf('78', plain,
% 3.13/3.35      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.13/3.35         (~ (v1_funct_1 @ X4)
% 3.13/3.35          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 3.13/3.35          | ~ (m1_subset_1 @ X4 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 3.13/3.35          | ~ (r3_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.35          | (r1_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.35          | ~ (m1_subset_1 @ X6 @ X5))),
% 3.13/3.35      inference('cnf', [status(esa)], [d7_binop_1])).
% 3.13/3.35  thf('79', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.35          | (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35          | ~ (r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35          | ~ (v1_funct_2 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F) @ 
% 3.13/3.35               (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35                (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 3.13/3.35               (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.35          | ~ (v1_funct_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['77', '78'])).
% 3.13/3.35  thf('80', plain,
% 3.13/3.35      ((v1_funct_2 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F) @ 
% 3.13/3.35        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 3.13/3.35        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.13/3.35      inference('demod', [status(thm)], ['24', '25', '26'])).
% 3.13/3.35  thf('81', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.35          | (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35          | ~ (r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35          | ~ (v1_funct_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.35      inference('demod', [status(thm)], ['79', '80'])).
% 3.13/3.35  thf('82', plain, ((v1_funct_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))),
% 3.13/3.35      inference('demod', [status(thm)], ['36', '37', '38'])).
% 3.13/3.35  thf('83', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.35          | (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35          | ~ (r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.35      inference('demod', [status(thm)], ['81', '82'])).
% 3.13/3.35  thf('84', plain,
% 3.13/3.35      ((((r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35          (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35          (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35         | ~ (m1_subset_1 @ (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35              (k2_zfmisc_1 @ sk_A @ sk_B))))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['76', '83'])).
% 3.13/3.35  thf('85', plain,
% 3.13/3.35      ((m1_subset_1 @ (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.13/3.35      inference('clc', [status(thm)], ['48', '49'])).
% 3.13/3.35  thf('86', plain,
% 3.13/3.35      (((r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('demod', [status(thm)], ['84', '85'])).
% 3.13/3.35  thf('87', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_F @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf(t25_filter_1, axiom,
% 3.13/3.35    (![A:$i]:
% 3.13/3.35     ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.13/3.35       ( ![B:$i]:
% 3.13/3.35         ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.13/3.35           ( ![C:$i]:
% 3.13/3.35             ( ( m1_subset_1 @ C @ A ) =>
% 3.13/3.35               ( ![D:$i]:
% 3.13/3.35                 ( ( m1_subset_1 @ D @ B ) =>
% 3.13/3.35                   ( ![E:$i]:
% 3.13/3.35                     ( ( ( v1_funct_1 @ E ) & 
% 3.13/3.35                         ( v1_funct_2 @ E @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 3.13/3.35                         ( m1_subset_1 @
% 3.13/3.35                           E @ 
% 3.13/3.35                           ( k1_zfmisc_1 @
% 3.13/3.35                             ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 3.13/3.35                       ( ![F:$i]:
% 3.13/3.35                         ( ( ( v1_funct_1 @ F ) & 
% 3.13/3.35                             ( v1_funct_2 @ F @ ( k2_zfmisc_1 @ B @ B ) @ B ) & 
% 3.13/3.35                             ( m1_subset_1 @
% 3.13/3.35                               F @ 
% 3.13/3.35                               ( k1_zfmisc_1 @
% 3.13/3.35                                 ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) ) =>
% 3.13/3.35                           ( ( ( r1_binop_1 @ A @ C @ E ) & 
% 3.13/3.35                               ( r1_binop_1 @ B @ D @ F ) ) <=>
% 3.13/3.35                             ( r1_binop_1 @
% 3.13/3.35                               ( k2_zfmisc_1 @ A @ B ) @ 
% 3.13/3.35                               ( k1_domain_1 @ A @ B @ C @ D ) @ 
% 3.13/3.35                               ( k6_filter_1 @ A @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.13/3.35  thf('88', plain,
% 3.13/3.35      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 3.13/3.35         ((v1_xboole_0 @ X11)
% 3.13/3.35          | ~ (m1_subset_1 @ X12 @ X11)
% 3.13/3.35          | ~ (v1_funct_1 @ X13)
% 3.13/3.35          | ~ (v1_funct_2 @ X13 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)
% 3.13/3.35          | ~ (m1_subset_1 @ X13 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)))
% 3.13/3.35          | ~ (r1_binop_1 @ (k2_zfmisc_1 @ X14 @ X11) @ 
% 3.13/3.35               (k1_domain_1 @ X14 @ X11 @ X15 @ X12) @ 
% 3.13/3.35               (k6_filter_1 @ X14 @ X11 @ X16 @ X13))
% 3.13/3.35          | (r1_binop_1 @ X11 @ X12 @ X13)
% 3.13/3.35          | ~ (m1_subset_1 @ X16 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)))
% 3.13/3.35          | ~ (v1_funct_2 @ X16 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)
% 3.13/3.35          | ~ (v1_funct_1 @ X16)
% 3.13/3.35          | ~ (m1_subset_1 @ X15 @ X14)
% 3.13/3.35          | (v1_xboole_0 @ X14))),
% 3.13/3.35      inference('cnf', [status(esa)], [t25_filter_1])).
% 3.13/3.35  thf('89', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.35         ((v1_xboole_0 @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ X2)
% 3.13/3.35          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.35          | (r1_binop_1 @ sk_B @ X3 @ sk_F)
% 3.13/3.35          | ~ (r1_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.35               (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.35          | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_F)
% 3.13/3.35          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.35          | (v1_xboole_0 @ sk_B))),
% 3.13/3.35      inference('sup-', [status(thm)], ['87', '88'])).
% 3.13/3.35  thf('90', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('91', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('92', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.35         ((v1_xboole_0 @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ X2)
% 3.13/3.35          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.35          | (r1_binop_1 @ sk_B @ X3 @ sk_F)
% 3.13/3.35          | ~ (r1_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.35               (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.35          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.35          | (v1_xboole_0 @ sk_B))),
% 3.13/3.35      inference('demod', [status(thm)], ['89', '90', '91'])).
% 3.13/3.35  thf('93', plain,
% 3.13/3.35      ((((v1_xboole_0 @ sk_B)
% 3.13/3.35         | ~ (m1_subset_1 @ sk_D @ sk_B)
% 3.13/3.35         | (r1_binop_1 @ sk_B @ sk_D @ sk_F)
% 3.13/3.35         | ~ (m1_subset_1 @ sk_E @ 
% 3.13/3.35              (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 3.13/3.35         | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 3.13/3.35         | ~ (v1_funct_1 @ sk_E)
% 3.13/3.35         | ~ (m1_subset_1 @ sk_C @ sk_A)
% 3.13/3.35         | (v1_xboole_0 @ sk_A)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['86', '92'])).
% 3.13/3.35  thf('94', plain, ((m1_subset_1 @ sk_D @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('95', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_E @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('96', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('97', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('98', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('99', plain,
% 3.13/3.35      ((((v1_xboole_0 @ sk_B)
% 3.13/3.35         | (r1_binop_1 @ sk_B @ sk_D @ sk_F)
% 3.13/3.35         | (v1_xboole_0 @ sk_A)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('demod', [status(thm)], ['93', '94', '95', '96', '97', '98'])).
% 3.13/3.35  thf('100', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('101', plain,
% 3.13/3.35      ((((v1_xboole_0 @ sk_A) | (r1_binop_1 @ sk_B @ sk_D @ sk_F)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('clc', [status(thm)], ['99', '100'])).
% 3.13/3.35  thf('102', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('103', plain,
% 3.13/3.35      (((r1_binop_1 @ sk_B @ sk_D @ sk_F))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('clc', [status(thm)], ['101', '102'])).
% 3.13/3.35  thf('104', plain, ((m1_subset_1 @ sk_D @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('105', plain,
% 3.13/3.35      (((r3_binop_1 @ sk_B @ sk_D @ sk_F))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('demod', [status(thm)], ['75', '103', '104'])).
% 3.13/3.35  thf('106', plain,
% 3.13/3.35      ((~ (r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35           (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35           (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.35        | ~ (r3_binop_1 @ sk_B @ sk_D @ sk_F)
% 3.13/3.35        | ~ (r3_binop_1 @ sk_A @ sk_C @ sk_E))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('107', plain,
% 3.13/3.35      ((~ (r3_binop_1 @ sk_B @ sk_D @ sk_F))
% 3.13/3.35         <= (~ ((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.35      inference('split', [status(esa)], ['106'])).
% 3.13/3.35  thf('108', plain,
% 3.13/3.35      (~
% 3.13/3.35       ((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))) | 
% 3.13/3.35       ((r3_binop_1 @ sk_B @ sk_D @ sk_F))),
% 3.13/3.35      inference('sup-', [status(thm)], ['105', '107'])).
% 3.13/3.35  thf('109', plain,
% 3.13/3.35      (((r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('demod', [status(thm)], ['41', '50'])).
% 3.13/3.35  thf('110', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_F @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('111', plain,
% 3.13/3.35      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.13/3.35         ((v1_xboole_0 @ X17)
% 3.13/3.35          | ~ (m1_subset_1 @ X18 @ X17)
% 3.13/3.35          | ~ (v1_funct_1 @ X19)
% 3.13/3.35          | ~ (v1_funct_2 @ X19 @ (k2_zfmisc_1 @ X17 @ X17) @ X17)
% 3.13/3.35          | ~ (m1_subset_1 @ X19 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17) @ X17)))
% 3.13/3.35          | ~ (r2_binop_1 @ (k2_zfmisc_1 @ X20 @ X17) @ 
% 3.13/3.35               (k1_domain_1 @ X20 @ X17 @ X21 @ X18) @ 
% 3.13/3.35               (k6_filter_1 @ X20 @ X17 @ X22 @ X19))
% 3.13/3.35          | (r2_binop_1 @ X20 @ X21 @ X22)
% 3.13/3.35          | ~ (m1_subset_1 @ X22 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20) @ X20)))
% 3.13/3.35          | ~ (v1_funct_2 @ X22 @ (k2_zfmisc_1 @ X20 @ X20) @ X20)
% 3.13/3.35          | ~ (v1_funct_1 @ X22)
% 3.13/3.35          | ~ (m1_subset_1 @ X21 @ X20)
% 3.13/3.35          | (v1_xboole_0 @ X20))),
% 3.13/3.35      inference('cnf', [status(esa)], [t26_filter_1])).
% 3.13/3.35  thf('112', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.35         ((v1_xboole_0 @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ X2)
% 3.13/3.35          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.35          | (r2_binop_1 @ X0 @ X1 @ X2)
% 3.13/3.35          | ~ (r2_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.35               (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.35          | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_F)
% 3.13/3.35          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.35          | (v1_xboole_0 @ sk_B))),
% 3.13/3.35      inference('sup-', [status(thm)], ['110', '111'])).
% 3.13/3.35  thf('113', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('114', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('115', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.35         ((v1_xboole_0 @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ X2)
% 3.13/3.35          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.35          | (r2_binop_1 @ X0 @ X1 @ X2)
% 3.13/3.35          | ~ (r2_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.35               (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.35          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.35          | (v1_xboole_0 @ sk_B))),
% 3.13/3.35      inference('demod', [status(thm)], ['112', '113', '114'])).
% 3.13/3.35  thf('116', plain,
% 3.13/3.35      ((((v1_xboole_0 @ sk_B)
% 3.13/3.35         | ~ (m1_subset_1 @ sk_D @ sk_B)
% 3.13/3.35         | (r2_binop_1 @ sk_A @ sk_C @ sk_E)
% 3.13/3.35         | ~ (m1_subset_1 @ sk_E @ 
% 3.13/3.35              (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 3.13/3.35         | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 3.13/3.35         | ~ (v1_funct_1 @ sk_E)
% 3.13/3.35         | ~ (m1_subset_1 @ sk_C @ sk_A)
% 3.13/3.35         | (v1_xboole_0 @ sk_A)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['109', '115'])).
% 3.13/3.35  thf('117', plain, ((m1_subset_1 @ sk_D @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('118', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_E @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('119', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('120', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('121', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('122', plain,
% 3.13/3.35      ((((v1_xboole_0 @ sk_B)
% 3.13/3.35         | (r2_binop_1 @ sk_A @ sk_C @ sk_E)
% 3.13/3.35         | (v1_xboole_0 @ sk_A)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('demod', [status(thm)],
% 3.13/3.35                ['116', '117', '118', '119', '120', '121'])).
% 3.13/3.35  thf('123', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('124', plain,
% 3.13/3.35      ((((v1_xboole_0 @ sk_A) | (r2_binop_1 @ sk_A @ sk_C @ sk_E)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('clc', [status(thm)], ['122', '123'])).
% 3.13/3.35  thf('125', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('126', plain,
% 3.13/3.35      (((r2_binop_1 @ sk_A @ sk_C @ sk_E))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('clc', [status(thm)], ['124', '125'])).
% 3.13/3.35  thf('127', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_E @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('128', plain,
% 3.13/3.35      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.13/3.35         (~ (v1_funct_1 @ X4)
% 3.13/3.35          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 3.13/3.35          | ~ (m1_subset_1 @ X4 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 3.13/3.35          | ~ (r1_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.35          | ~ (r2_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.35          | (r3_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.35          | ~ (m1_subset_1 @ X6 @ X5))),
% 3.13/3.35      inference('cnf', [status(esa)], [d7_binop_1])).
% 3.13/3.35  thf('129', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ sk_A)
% 3.13/3.35          | (r3_binop_1 @ sk_A @ X0 @ sk_E)
% 3.13/3.35          | ~ (r2_binop_1 @ sk_A @ X0 @ sk_E)
% 3.13/3.35          | ~ (r1_binop_1 @ sk_A @ X0 @ sk_E)
% 3.13/3.35          | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_E))),
% 3.13/3.35      inference('sup-', [status(thm)], ['127', '128'])).
% 3.13/3.35  thf('130', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('131', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('132', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ sk_A)
% 3.13/3.35          | (r3_binop_1 @ sk_A @ X0 @ sk_E)
% 3.13/3.35          | ~ (r2_binop_1 @ sk_A @ X0 @ sk_E)
% 3.13/3.35          | ~ (r1_binop_1 @ sk_A @ X0 @ sk_E))),
% 3.13/3.35      inference('demod', [status(thm)], ['129', '130', '131'])).
% 3.13/3.35  thf('133', plain,
% 3.13/3.35      (((~ (r1_binop_1 @ sk_A @ sk_C @ sk_E)
% 3.13/3.35         | (r3_binop_1 @ sk_A @ sk_C @ sk_E)
% 3.13/3.35         | ~ (m1_subset_1 @ sk_C @ sk_A)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['126', '132'])).
% 3.13/3.35  thf('134', plain,
% 3.13/3.35      (((r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))
% 3.13/3.35         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.35               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.35      inference('demod', [status(thm)], ['84', '85'])).
% 3.13/3.35  thf('135', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_F @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('136', plain,
% 3.13/3.35      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 3.13/3.35         ((v1_xboole_0 @ X11)
% 3.13/3.35          | ~ (m1_subset_1 @ X12 @ X11)
% 3.13/3.35          | ~ (v1_funct_1 @ X13)
% 3.13/3.35          | ~ (v1_funct_2 @ X13 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)
% 3.13/3.35          | ~ (m1_subset_1 @ X13 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)))
% 3.13/3.35          | ~ (r1_binop_1 @ (k2_zfmisc_1 @ X14 @ X11) @ 
% 3.13/3.35               (k1_domain_1 @ X14 @ X11 @ X15 @ X12) @ 
% 3.13/3.35               (k6_filter_1 @ X14 @ X11 @ X16 @ X13))
% 3.13/3.35          | (r1_binop_1 @ X14 @ X15 @ X16)
% 3.13/3.35          | ~ (m1_subset_1 @ X16 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)))
% 3.13/3.35          | ~ (v1_funct_2 @ X16 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)
% 3.13/3.35          | ~ (v1_funct_1 @ X16)
% 3.13/3.35          | ~ (m1_subset_1 @ X15 @ X14)
% 3.13/3.35          | (v1_xboole_0 @ X14))),
% 3.13/3.35      inference('cnf', [status(esa)], [t25_filter_1])).
% 3.13/3.35  thf('137', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.35         ((v1_xboole_0 @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ X2)
% 3.13/3.35          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.35          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.35          | (r1_binop_1 @ X0 @ X1 @ X2)
% 3.13/3.35          | ~ (r1_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.35               (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.35               (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.35          | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_F)
% 3.13/3.35          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.35          | (v1_xboole_0 @ sk_B))),
% 3.13/3.35      inference('sup-', [status(thm)], ['135', '136'])).
% 3.13/3.35  thf('138', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('139', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('140', plain,
% 3.13/3.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.36         ((v1_xboole_0 @ X0)
% 3.13/3.36          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.36          | ~ (v1_funct_1 @ X2)
% 3.13/3.36          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.36          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.36          | (r1_binop_1 @ X0 @ X1 @ X2)
% 3.13/3.36          | ~ (r1_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.36               (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.36               (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.36          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.36          | (v1_xboole_0 @ sk_B))),
% 3.13/3.36      inference('demod', [status(thm)], ['137', '138', '139'])).
% 3.13/3.36  thf('141', plain,
% 3.13/3.36      ((((v1_xboole_0 @ sk_B)
% 3.13/3.36         | ~ (m1_subset_1 @ sk_D @ sk_B)
% 3.13/3.36         | (r1_binop_1 @ sk_A @ sk_C @ sk_E)
% 3.13/3.36         | ~ (m1_subset_1 @ sk_E @ 
% 3.13/3.36              (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 3.13/3.36         | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 3.13/3.36         | ~ (v1_funct_1 @ sk_E)
% 3.13/3.36         | ~ (m1_subset_1 @ sk_C @ sk_A)
% 3.13/3.36         | (v1_xboole_0 @ sk_A)))
% 3.13/3.36         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.36      inference('sup-', [status(thm)], ['134', '140'])).
% 3.13/3.36  thf('142', plain, ((m1_subset_1 @ sk_D @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('143', plain,
% 3.13/3.36      ((m1_subset_1 @ sk_E @ 
% 3.13/3.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('144', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('145', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('146', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('147', plain,
% 3.13/3.36      ((((v1_xboole_0 @ sk_B)
% 3.13/3.36         | (r1_binop_1 @ sk_A @ sk_C @ sk_E)
% 3.13/3.36         | (v1_xboole_0 @ sk_A)))
% 3.13/3.36         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.36      inference('demod', [status(thm)],
% 3.13/3.36                ['141', '142', '143', '144', '145', '146'])).
% 3.13/3.36  thf('148', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('149', plain,
% 3.13/3.36      ((((v1_xboole_0 @ sk_A) | (r1_binop_1 @ sk_A @ sk_C @ sk_E)))
% 3.13/3.36         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.36      inference('clc', [status(thm)], ['147', '148'])).
% 3.13/3.36  thf('150', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('151', plain,
% 3.13/3.36      (((r1_binop_1 @ sk_A @ sk_C @ sk_E))
% 3.13/3.36         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.36      inference('clc', [status(thm)], ['149', '150'])).
% 3.13/3.36  thf('152', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('153', plain,
% 3.13/3.36      (((r3_binop_1 @ sk_A @ sk_C @ sk_E))
% 3.13/3.36         <= (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.36      inference('demod', [status(thm)], ['133', '151', '152'])).
% 3.13/3.36  thf('154', plain,
% 3.13/3.36      ((~ (r3_binop_1 @ sk_A @ sk_C @ sk_E))
% 3.13/3.36         <= (~ ((r3_binop_1 @ sk_A @ sk_C @ sk_E)))),
% 3.13/3.36      inference('split', [status(esa)], ['106'])).
% 3.13/3.36  thf('155', plain,
% 3.13/3.36      (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) | 
% 3.13/3.36       ~
% 3.13/3.36       ((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.36      inference('sup-', [status(thm)], ['153', '154'])).
% 3.13/3.36  thf('156', plain,
% 3.13/3.36      (~
% 3.13/3.36       ((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))) | 
% 3.13/3.36       ~ ((r3_binop_1 @ sk_B @ sk_D @ sk_F)) | 
% 3.13/3.36       ~ ((r3_binop_1 @ sk_A @ sk_C @ sk_E))),
% 3.13/3.36      inference('split', [status(esa)], ['106'])).
% 3.13/3.36  thf('157', plain,
% 3.13/3.36      (((r3_binop_1 @ sk_B @ sk_D @ sk_F))
% 3.13/3.36         <= (((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('split', [status(esa)], ['0'])).
% 3.13/3.36  thf('158', plain,
% 3.13/3.36      ((m1_subset_1 @ sk_F @ 
% 3.13/3.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('159', plain,
% 3.13/3.36      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.13/3.36         (~ (v1_funct_1 @ X4)
% 3.13/3.36          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 3.13/3.36          | ~ (m1_subset_1 @ X4 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 3.13/3.36          | ~ (r3_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.36          | (r2_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.36          | ~ (m1_subset_1 @ X6 @ X5))),
% 3.13/3.36      inference('cnf', [status(esa)], [d7_binop_1])).
% 3.13/3.36  thf('160', plain,
% 3.13/3.36      (![X0 : $i]:
% 3.13/3.36         (~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36          | (r2_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36          | ~ (r3_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36          | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.36          | ~ (v1_funct_1 @ sk_F))),
% 3.13/3.36      inference('sup-', [status(thm)], ['158', '159'])).
% 3.13/3.36  thf('161', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('162', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('163', plain,
% 3.13/3.36      (![X0 : $i]:
% 3.13/3.36         (~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36          | (r2_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36          | ~ (r3_binop_1 @ sk_B @ X0 @ sk_F))),
% 3.13/3.36      inference('demod', [status(thm)], ['160', '161', '162'])).
% 3.13/3.36  thf('164', plain,
% 3.13/3.36      ((((r2_binop_1 @ sk_B @ sk_D @ sk_F) | ~ (m1_subset_1 @ sk_D @ sk_B)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('sup-', [status(thm)], ['157', '163'])).
% 3.13/3.36  thf('165', plain, ((m1_subset_1 @ sk_D @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('166', plain,
% 3.13/3.36      (((r2_binop_1 @ sk_B @ sk_D @ sk_F))
% 3.13/3.36         <= (((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('demod', [status(thm)], ['164', '165'])).
% 3.13/3.36  thf('167', plain,
% 3.13/3.36      (((r3_binop_1 @ sk_A @ sk_C @ sk_E))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)))),
% 3.13/3.36      inference('split', [status(esa)], ['2'])).
% 3.13/3.36  thf('168', plain,
% 3.13/3.36      ((m1_subset_1 @ sk_E @ 
% 3.13/3.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('169', plain,
% 3.13/3.36      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.13/3.36         (~ (v1_funct_1 @ X4)
% 3.13/3.36          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 3.13/3.36          | ~ (m1_subset_1 @ X4 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 3.13/3.36          | ~ (r3_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.36          | (r2_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.36          | ~ (m1_subset_1 @ X6 @ X5))),
% 3.13/3.36      inference('cnf', [status(esa)], [d7_binop_1])).
% 3.13/3.36  thf('170', plain,
% 3.13/3.36      (![X0 : $i]:
% 3.13/3.36         (~ (m1_subset_1 @ X0 @ sk_A)
% 3.13/3.36          | (r2_binop_1 @ sk_A @ X0 @ sk_E)
% 3.13/3.36          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_E)
% 3.13/3.36          | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 3.13/3.36          | ~ (v1_funct_1 @ sk_E))),
% 3.13/3.36      inference('sup-', [status(thm)], ['168', '169'])).
% 3.13/3.36  thf('171', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('172', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('173', plain,
% 3.13/3.36      (![X0 : $i]:
% 3.13/3.36         (~ (m1_subset_1 @ X0 @ sk_A)
% 3.13/3.36          | (r2_binop_1 @ sk_A @ X0 @ sk_E)
% 3.13/3.36          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_E))),
% 3.13/3.36      inference('demod', [status(thm)], ['170', '171', '172'])).
% 3.13/3.36  thf('174', plain,
% 3.13/3.36      ((((r2_binop_1 @ sk_A @ sk_C @ sk_E) | ~ (m1_subset_1 @ sk_C @ sk_A)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)))),
% 3.13/3.36      inference('sup-', [status(thm)], ['167', '173'])).
% 3.13/3.36  thf('175', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('176', plain,
% 3.13/3.36      (((r2_binop_1 @ sk_A @ sk_C @ sk_E))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)))),
% 3.13/3.36      inference('demod', [status(thm)], ['174', '175'])).
% 3.13/3.36  thf('177', plain,
% 3.13/3.36      ((m1_subset_1 @ sk_E @ 
% 3.13/3.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('178', plain,
% 3.13/3.36      ((m1_subset_1 @ sk_F @ 
% 3.13/3.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('179', plain,
% 3.13/3.36      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.13/3.36         ((v1_xboole_0 @ X17)
% 3.13/3.36          | ~ (m1_subset_1 @ X18 @ X17)
% 3.13/3.36          | ~ (v1_funct_1 @ X19)
% 3.13/3.36          | ~ (v1_funct_2 @ X19 @ (k2_zfmisc_1 @ X17 @ X17) @ X17)
% 3.13/3.36          | ~ (m1_subset_1 @ X19 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17) @ X17)))
% 3.13/3.36          | ~ (r2_binop_1 @ X20 @ X21 @ X22)
% 3.13/3.36          | ~ (r2_binop_1 @ X17 @ X18 @ X19)
% 3.13/3.36          | (r2_binop_1 @ (k2_zfmisc_1 @ X20 @ X17) @ 
% 3.13/3.36             (k1_domain_1 @ X20 @ X17 @ X21 @ X18) @ 
% 3.13/3.36             (k6_filter_1 @ X20 @ X17 @ X22 @ X19))
% 3.13/3.36          | ~ (m1_subset_1 @ X22 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20) @ X20)))
% 3.13/3.36          | ~ (v1_funct_2 @ X22 @ (k2_zfmisc_1 @ X20 @ X20) @ X20)
% 3.13/3.36          | ~ (v1_funct_1 @ X22)
% 3.13/3.36          | ~ (m1_subset_1 @ X21 @ X20)
% 3.13/3.36          | (v1_xboole_0 @ X20))),
% 3.13/3.36      inference('cnf', [status(esa)], [t26_filter_1])).
% 3.13/3.36  thf('180', plain,
% 3.13/3.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.36         ((v1_xboole_0 @ X0)
% 3.13/3.36          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.36          | ~ (v1_funct_1 @ X2)
% 3.13/3.36          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.36          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.36          | (r2_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.36             (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.36             (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.36          | ~ (r2_binop_1 @ sk_B @ X3 @ sk_F)
% 3.13/3.36          | ~ (r2_binop_1 @ X0 @ X1 @ X2)
% 3.13/3.36          | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.36          | ~ (v1_funct_1 @ sk_F)
% 3.13/3.36          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.36          | (v1_xboole_0 @ sk_B))),
% 3.13/3.36      inference('sup-', [status(thm)], ['178', '179'])).
% 3.13/3.36  thf('181', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('182', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('183', plain,
% 3.13/3.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.36         ((v1_xboole_0 @ X0)
% 3.13/3.36          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.36          | ~ (v1_funct_1 @ X2)
% 3.13/3.36          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.36          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.36          | (r2_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.36             (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.36             (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.36          | ~ (r2_binop_1 @ sk_B @ X3 @ sk_F)
% 3.13/3.36          | ~ (r2_binop_1 @ X0 @ X1 @ X2)
% 3.13/3.36          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.36          | (v1_xboole_0 @ sk_B))),
% 3.13/3.36      inference('demod', [status(thm)], ['180', '181', '182'])).
% 3.13/3.36  thf('184', plain,
% 3.13/3.36      (![X0 : $i, X1 : $i]:
% 3.13/3.36         ((v1_xboole_0 @ sk_B)
% 3.13/3.36          | ~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36          | ~ (r2_binop_1 @ sk_A @ X1 @ sk_E)
% 3.13/3.36          | ~ (r2_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36          | (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36             (k1_domain_1 @ sk_A @ sk_B @ X1 @ X0) @ 
% 3.13/3.36             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36          | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 3.13/3.36          | ~ (v1_funct_1 @ sk_E)
% 3.13/3.36          | ~ (m1_subset_1 @ X1 @ sk_A)
% 3.13/3.36          | (v1_xboole_0 @ sk_A))),
% 3.13/3.36      inference('sup-', [status(thm)], ['177', '183'])).
% 3.13/3.36  thf('185', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('186', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('187', plain,
% 3.13/3.36      (![X0 : $i, X1 : $i]:
% 3.13/3.36         ((v1_xboole_0 @ sk_B)
% 3.13/3.36          | ~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36          | ~ (r2_binop_1 @ sk_A @ X1 @ sk_E)
% 3.13/3.36          | ~ (r2_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36          | (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36             (k1_domain_1 @ sk_A @ sk_B @ X1 @ X0) @ 
% 3.13/3.36             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36          | ~ (m1_subset_1 @ X1 @ sk_A)
% 3.13/3.36          | (v1_xboole_0 @ sk_A))),
% 3.13/3.36      inference('demod', [status(thm)], ['184', '185', '186'])).
% 3.13/3.36  thf('188', plain,
% 3.13/3.36      ((![X0 : $i]:
% 3.13/3.36          ((v1_xboole_0 @ sk_A)
% 3.13/3.36           | ~ (m1_subset_1 @ sk_C @ sk_A)
% 3.13/3.36           | (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36              (k1_domain_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 3.13/3.36              (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36           | ~ (r2_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36           | ~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36           | (v1_xboole_0 @ sk_B)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)))),
% 3.13/3.36      inference('sup-', [status(thm)], ['176', '187'])).
% 3.13/3.36  thf('189', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('190', plain,
% 3.13/3.36      ((![X0 : $i]:
% 3.13/3.36          ((v1_xboole_0 @ sk_A)
% 3.13/3.36           | (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36              (k1_domain_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 3.13/3.36              (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36           | ~ (r2_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36           | ~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36           | (v1_xboole_0 @ sk_B)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)))),
% 3.13/3.36      inference('demod', [status(thm)], ['188', '189'])).
% 3.13/3.36  thf('191', plain,
% 3.13/3.36      ((((v1_xboole_0 @ sk_B)
% 3.13/3.36         | ~ (m1_subset_1 @ sk_D @ sk_B)
% 3.13/3.36         | (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36            (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36            (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36         | (v1_xboole_0 @ sk_A)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) & 
% 3.13/3.36             ((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('sup-', [status(thm)], ['166', '190'])).
% 3.13/3.36  thf('192', plain, ((m1_subset_1 @ sk_D @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('193', plain,
% 3.13/3.36      ((((v1_xboole_0 @ sk_B)
% 3.13/3.36         | (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36            (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36            (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36         | (v1_xboole_0 @ sk_A)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) & 
% 3.13/3.36             ((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('demod', [status(thm)], ['191', '192'])).
% 3.13/3.36  thf('194', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('195', plain,
% 3.13/3.36      ((((v1_xboole_0 @ sk_A)
% 3.13/3.36         | (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36            (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36            (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) & 
% 3.13/3.36             ((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('clc', [status(thm)], ['193', '194'])).
% 3.13/3.36  thf('196', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('197', plain,
% 3.13/3.36      (((r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) & 
% 3.13/3.36             ((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('clc', [status(thm)], ['195', '196'])).
% 3.13/3.36  thf('198', plain,
% 3.13/3.36      ((m1_subset_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F) @ 
% 3.13/3.36        (k1_zfmisc_1 @ 
% 3.13/3.36         (k2_zfmisc_1 @ 
% 3.13/3.36          (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36           (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 3.13/3.36          (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 3.13/3.36      inference('demod', [status(thm)], ['11', '12', '13'])).
% 3.13/3.36  thf('199', plain,
% 3.13/3.36      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.13/3.36         (~ (v1_funct_1 @ X4)
% 3.13/3.36          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 3.13/3.36          | ~ (m1_subset_1 @ X4 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 3.13/3.36          | ~ (r1_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.36          | ~ (r2_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.36          | (r3_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.36          | ~ (m1_subset_1 @ X6 @ X5))),
% 3.13/3.36      inference('cnf', [status(esa)], [d7_binop_1])).
% 3.13/3.36  thf('200', plain,
% 3.13/3.36      (![X0 : $i]:
% 3.13/3.36         (~ (m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.36          | (r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.36             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36          | ~ (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.36               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36          | ~ (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.36               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36          | ~ (v1_funct_2 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F) @ 
% 3.13/3.36               (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36                (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 3.13/3.36               (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.36          | ~ (v1_funct_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.36      inference('sup-', [status(thm)], ['198', '199'])).
% 3.13/3.36  thf('201', plain,
% 3.13/3.36      ((v1_funct_2 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F) @ 
% 3.13/3.36        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36         (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 3.13/3.36        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.13/3.36      inference('demod', [status(thm)], ['24', '25', '26'])).
% 3.13/3.36  thf('202', plain, ((v1_funct_1 @ (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))),
% 3.13/3.36      inference('demod', [status(thm)], ['36', '37', '38'])).
% 3.13/3.36  thf('203', plain,
% 3.13/3.36      (![X0 : $i]:
% 3.13/3.36         (~ (m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.13/3.36          | (r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.36             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36          | ~ (r2_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.36               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36          | ~ (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ 
% 3.13/3.36               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.36      inference('demod', [status(thm)], ['200', '201', '202'])).
% 3.13/3.36  thf('204', plain,
% 3.13/3.36      (((~ (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36            (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36            (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36         | (r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36            (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36            (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36         | ~ (m1_subset_1 @ (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36              (k2_zfmisc_1 @ sk_A @ sk_B))))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) & 
% 3.13/3.36             ((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('sup-', [status(thm)], ['197', '203'])).
% 3.13/3.36  thf('205', plain,
% 3.13/3.36      (((r3_binop_1 @ sk_B @ sk_D @ sk_F))
% 3.13/3.36         <= (((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('split', [status(esa)], ['0'])).
% 3.13/3.36  thf('206', plain,
% 3.13/3.36      ((m1_subset_1 @ sk_F @ 
% 3.13/3.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('207', plain,
% 3.13/3.36      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.13/3.36         (~ (v1_funct_1 @ X4)
% 3.13/3.36          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 3.13/3.36          | ~ (m1_subset_1 @ X4 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 3.13/3.36          | ~ (r3_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.36          | (r1_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.36          | ~ (m1_subset_1 @ X6 @ X5))),
% 3.13/3.36      inference('cnf', [status(esa)], [d7_binop_1])).
% 3.13/3.36  thf('208', plain,
% 3.13/3.36      (![X0 : $i]:
% 3.13/3.36         (~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36          | (r1_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36          | ~ (r3_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36          | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.36          | ~ (v1_funct_1 @ sk_F))),
% 3.13/3.36      inference('sup-', [status(thm)], ['206', '207'])).
% 3.13/3.36  thf('209', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('210', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('211', plain,
% 3.13/3.36      (![X0 : $i]:
% 3.13/3.36         (~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36          | (r1_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36          | ~ (r3_binop_1 @ sk_B @ X0 @ sk_F))),
% 3.13/3.36      inference('demod', [status(thm)], ['208', '209', '210'])).
% 3.13/3.36  thf('212', plain,
% 3.13/3.36      ((((r1_binop_1 @ sk_B @ sk_D @ sk_F) | ~ (m1_subset_1 @ sk_D @ sk_B)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('sup-', [status(thm)], ['205', '211'])).
% 3.13/3.36  thf('213', plain, ((m1_subset_1 @ sk_D @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('214', plain,
% 3.13/3.36      (((r1_binop_1 @ sk_B @ sk_D @ sk_F))
% 3.13/3.36         <= (((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('demod', [status(thm)], ['212', '213'])).
% 3.13/3.36  thf('215', plain,
% 3.13/3.36      (((r3_binop_1 @ sk_A @ sk_C @ sk_E))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)))),
% 3.13/3.36      inference('split', [status(esa)], ['2'])).
% 3.13/3.36  thf('216', plain,
% 3.13/3.36      ((m1_subset_1 @ sk_E @ 
% 3.13/3.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('217', plain,
% 3.13/3.36      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.13/3.36         (~ (v1_funct_1 @ X4)
% 3.13/3.36          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 3.13/3.36          | ~ (m1_subset_1 @ X4 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 3.13/3.36          | ~ (r3_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.36          | (r1_binop_1 @ X5 @ X6 @ X4)
% 3.13/3.36          | ~ (m1_subset_1 @ X6 @ X5))),
% 3.13/3.36      inference('cnf', [status(esa)], [d7_binop_1])).
% 3.13/3.36  thf('218', plain,
% 3.13/3.36      (![X0 : $i]:
% 3.13/3.36         (~ (m1_subset_1 @ X0 @ sk_A)
% 3.13/3.36          | (r1_binop_1 @ sk_A @ X0 @ sk_E)
% 3.13/3.36          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_E)
% 3.13/3.36          | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 3.13/3.36          | ~ (v1_funct_1 @ sk_E))),
% 3.13/3.36      inference('sup-', [status(thm)], ['216', '217'])).
% 3.13/3.36  thf('219', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('220', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('221', plain,
% 3.13/3.36      (![X0 : $i]:
% 3.13/3.36         (~ (m1_subset_1 @ X0 @ sk_A)
% 3.13/3.36          | (r1_binop_1 @ sk_A @ X0 @ sk_E)
% 3.13/3.36          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_E))),
% 3.13/3.36      inference('demod', [status(thm)], ['218', '219', '220'])).
% 3.13/3.36  thf('222', plain,
% 3.13/3.36      ((((r1_binop_1 @ sk_A @ sk_C @ sk_E) | ~ (m1_subset_1 @ sk_C @ sk_A)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)))),
% 3.13/3.36      inference('sup-', [status(thm)], ['215', '221'])).
% 3.13/3.36  thf('223', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('224', plain,
% 3.13/3.36      (((r1_binop_1 @ sk_A @ sk_C @ sk_E))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)))),
% 3.13/3.36      inference('demod', [status(thm)], ['222', '223'])).
% 3.13/3.36  thf('225', plain,
% 3.13/3.36      ((m1_subset_1 @ sk_E @ 
% 3.13/3.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('226', plain,
% 3.13/3.36      ((m1_subset_1 @ sk_F @ 
% 3.13/3.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)))),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('227', plain,
% 3.13/3.36      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 3.13/3.36         ((v1_xboole_0 @ X11)
% 3.13/3.36          | ~ (m1_subset_1 @ X12 @ X11)
% 3.13/3.36          | ~ (v1_funct_1 @ X13)
% 3.13/3.36          | ~ (v1_funct_2 @ X13 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)
% 3.13/3.36          | ~ (m1_subset_1 @ X13 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)))
% 3.13/3.36          | ~ (r1_binop_1 @ X14 @ X15 @ X16)
% 3.13/3.36          | ~ (r1_binop_1 @ X11 @ X12 @ X13)
% 3.13/3.36          | (r1_binop_1 @ (k2_zfmisc_1 @ X14 @ X11) @ 
% 3.13/3.36             (k1_domain_1 @ X14 @ X11 @ X15 @ X12) @ 
% 3.13/3.36             (k6_filter_1 @ X14 @ X11 @ X16 @ X13))
% 3.13/3.36          | ~ (m1_subset_1 @ X16 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)))
% 3.13/3.36          | ~ (v1_funct_2 @ X16 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)
% 3.13/3.36          | ~ (v1_funct_1 @ X16)
% 3.13/3.36          | ~ (m1_subset_1 @ X15 @ X14)
% 3.13/3.36          | (v1_xboole_0 @ X14))),
% 3.13/3.36      inference('cnf', [status(esa)], [t25_filter_1])).
% 3.13/3.36  thf('228', plain,
% 3.13/3.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.36         ((v1_xboole_0 @ X0)
% 3.13/3.36          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.36          | ~ (v1_funct_1 @ X2)
% 3.13/3.36          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.36          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.36          | (r1_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.36             (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.36             (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.36          | ~ (r1_binop_1 @ sk_B @ X3 @ sk_F)
% 3.13/3.36          | ~ (r1_binop_1 @ X0 @ X1 @ X2)
% 3.13/3.36          | ~ (v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)
% 3.13/3.36          | ~ (v1_funct_1 @ sk_F)
% 3.13/3.36          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.36          | (v1_xboole_0 @ sk_B))),
% 3.13/3.36      inference('sup-', [status(thm)], ['226', '227'])).
% 3.13/3.36  thf('229', plain, ((v1_funct_2 @ sk_F @ (k2_zfmisc_1 @ sk_B @ sk_B) @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('230', plain, ((v1_funct_1 @ sk_F)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('231', plain,
% 3.13/3.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.13/3.36         ((v1_xboole_0 @ X0)
% 3.13/3.36          | ~ (m1_subset_1 @ X1 @ X0)
% 3.13/3.36          | ~ (v1_funct_1 @ X2)
% 3.13/3.36          | ~ (v1_funct_2 @ X2 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)
% 3.13/3.36          | ~ (m1_subset_1 @ X2 @ 
% 3.13/3.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0) @ X0)))
% 3.13/3.36          | (r1_binop_1 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 3.13/3.36             (k1_domain_1 @ X0 @ sk_B @ X1 @ X3) @ 
% 3.13/3.36             (k6_filter_1 @ X0 @ sk_B @ X2 @ sk_F))
% 3.13/3.36          | ~ (r1_binop_1 @ sk_B @ X3 @ sk_F)
% 3.13/3.36          | ~ (r1_binop_1 @ X0 @ X1 @ X2)
% 3.13/3.36          | ~ (m1_subset_1 @ X3 @ sk_B)
% 3.13/3.36          | (v1_xboole_0 @ sk_B))),
% 3.13/3.36      inference('demod', [status(thm)], ['228', '229', '230'])).
% 3.13/3.36  thf('232', plain,
% 3.13/3.36      (![X0 : $i, X1 : $i]:
% 3.13/3.36         ((v1_xboole_0 @ sk_B)
% 3.13/3.36          | ~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36          | ~ (r1_binop_1 @ sk_A @ X1 @ sk_E)
% 3.13/3.36          | ~ (r1_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36          | (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36             (k1_domain_1 @ sk_A @ sk_B @ X1 @ X0) @ 
% 3.13/3.36             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36          | ~ (v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 3.13/3.36          | ~ (v1_funct_1 @ sk_E)
% 3.13/3.36          | ~ (m1_subset_1 @ X1 @ sk_A)
% 3.13/3.36          | (v1_xboole_0 @ sk_A))),
% 3.13/3.36      inference('sup-', [status(thm)], ['225', '231'])).
% 3.13/3.36  thf('233', plain, ((v1_funct_2 @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('234', plain, ((v1_funct_1 @ sk_E)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('235', plain,
% 3.13/3.36      (![X0 : $i, X1 : $i]:
% 3.13/3.36         ((v1_xboole_0 @ sk_B)
% 3.13/3.36          | ~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36          | ~ (r1_binop_1 @ sk_A @ X1 @ sk_E)
% 3.13/3.36          | ~ (r1_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36          | (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36             (k1_domain_1 @ sk_A @ sk_B @ X1 @ X0) @ 
% 3.13/3.36             (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36          | ~ (m1_subset_1 @ X1 @ sk_A)
% 3.13/3.36          | (v1_xboole_0 @ sk_A))),
% 3.13/3.36      inference('demod', [status(thm)], ['232', '233', '234'])).
% 3.13/3.36  thf('236', plain,
% 3.13/3.36      ((![X0 : $i]:
% 3.13/3.36          ((v1_xboole_0 @ sk_A)
% 3.13/3.36           | ~ (m1_subset_1 @ sk_C @ sk_A)
% 3.13/3.36           | (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36              (k1_domain_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 3.13/3.36              (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36           | ~ (r1_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36           | ~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36           | (v1_xboole_0 @ sk_B)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)))),
% 3.13/3.36      inference('sup-', [status(thm)], ['224', '235'])).
% 3.13/3.36  thf('237', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('238', plain,
% 3.13/3.36      ((![X0 : $i]:
% 3.13/3.36          ((v1_xboole_0 @ sk_A)
% 3.13/3.36           | (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36              (k1_domain_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 3.13/3.36              (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36           | ~ (r1_binop_1 @ sk_B @ X0 @ sk_F)
% 3.13/3.36           | ~ (m1_subset_1 @ X0 @ sk_B)
% 3.13/3.36           | (v1_xboole_0 @ sk_B)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)))),
% 3.13/3.36      inference('demod', [status(thm)], ['236', '237'])).
% 3.13/3.36  thf('239', plain,
% 3.13/3.36      ((((v1_xboole_0 @ sk_B)
% 3.13/3.36         | ~ (m1_subset_1 @ sk_D @ sk_B)
% 3.13/3.36         | (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36            (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36            (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36         | (v1_xboole_0 @ sk_A)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) & 
% 3.13/3.36             ((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('sup-', [status(thm)], ['214', '238'])).
% 3.13/3.36  thf('240', plain, ((m1_subset_1 @ sk_D @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('241', plain,
% 3.13/3.36      ((((v1_xboole_0 @ sk_B)
% 3.13/3.36         | (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36            (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36            (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))
% 3.13/3.36         | (v1_xboole_0 @ sk_A)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) & 
% 3.13/3.36             ((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('demod', [status(thm)], ['239', '240'])).
% 3.13/3.36  thf('242', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('243', plain,
% 3.13/3.36      ((((v1_xboole_0 @ sk_A)
% 3.13/3.36         | (r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36            (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36            (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) & 
% 3.13/3.36             ((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('clc', [status(thm)], ['241', '242'])).
% 3.13/3.36  thf('244', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.13/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.36  thf('245', plain,
% 3.13/3.36      (((r1_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) & 
% 3.13/3.36             ((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('clc', [status(thm)], ['243', '244'])).
% 3.13/3.36  thf('246', plain,
% 3.13/3.36      ((m1_subset_1 @ (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.13/3.36      inference('clc', [status(thm)], ['48', '49'])).
% 3.13/3.36  thf('247', plain,
% 3.13/3.36      (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))
% 3.13/3.36         <= (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) & 
% 3.13/3.36             ((r3_binop_1 @ sk_B @ sk_D @ sk_F)))),
% 3.13/3.36      inference('demod', [status(thm)], ['204', '245', '246'])).
% 3.13/3.36  thf('248', plain,
% 3.13/3.36      ((~ (r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36           (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36           (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))
% 3.13/3.36         <= (~
% 3.13/3.36             ((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36               (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36               (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))))),
% 3.13/3.36      inference('split', [status(esa)], ['106'])).
% 3.13/3.36  thf('249', plain,
% 3.13/3.36      (((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F))) | 
% 3.13/3.36       ~ ((r3_binop_1 @ sk_A @ sk_C @ sk_E)) | 
% 3.13/3.36       ~ ((r3_binop_1 @ sk_B @ sk_D @ sk_F))),
% 3.13/3.36      inference('sup-', [status(thm)], ['247', '248'])).
% 3.13/3.36  thf('250', plain,
% 3.13/3.36      (((r3_binop_1 @ sk_A @ sk_C @ sk_E)) | 
% 3.13/3.36       ((r3_binop_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.13/3.36         (k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 3.13/3.36         (k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F)))),
% 3.13/3.36      inference('split', [status(esa)], ['2'])).
% 3.13/3.36  thf('251', plain, ($false),
% 3.13/3.36      inference('sat_resolution*', [status(thm)],
% 3.13/3.36                ['1', '108', '155', '156', '249', '250'])).
% 3.13/3.36  
% 3.13/3.36  % SZS output end Refutation
% 3.13/3.36  
% 3.13/3.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
