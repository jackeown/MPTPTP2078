%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1432+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mjT1BxDEsJ

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:39 EST 2020

% Result     : Theorem 3.25s
% Output     : Refutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  277 ( 906 expanded)
%              Number of leaves         :   23 ( 262 expanded)
%              Depth                    :   19
%              Number of atoms          : 4812 (35916 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_domain_1_type,type,(
    k1_domain_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_binop_1_type,type,(
    r1_binop_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_filter_1_type,type,(
    k6_filter_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_binop_1_type,type,(
    r2_binop_1: $i > $i > $i > $o )).

thf(r3_binop_1_type,type,(
    r3_binop_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( r3_binop_1 @ X1 @ X2 @ X0 )
      | ( r2_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X1 ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( m1_subset_1 @ ( k1_domain_1 @ X4 @ X5 @ X3 @ X6 ) @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( r1_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( r2_binop_1 @ X1 @ X2 @ X0 )
      | ( r3_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X1 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( r3_binop_1 @ X1 @ X2 @ X0 )
      | ( r1_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X1 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( r1_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( r2_binop_1 @ X1 @ X2 @ X0 )
      | ( r3_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X1 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( r3_binop_1 @ X1 @ X2 @ X0 )
      | ( r2_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X1 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( r3_binop_1 @ X1 @ X2 @ X0 )
      | ( r2_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X1 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( r1_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( r2_binop_1 @ X1 @ X2 @ X0 )
      | ( r3_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X1 ) ) ),
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
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( v1_funct_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,(
    v1_funct_1 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r2_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,
    ( ( ~ ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( m1_subset_1 @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['197','204'])).

thf('206',plain,
    ( ( r3_binop_1 @ sk_B @ sk_D @ sk_F )
   <= ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('207',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( r3_binop_1 @ X1 @ X2 @ X0 )
      | ( r1_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( r1_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( r3_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( r1_binop_1 @ sk_B @ X0 @ sk_F )
      | ~ ( r3_binop_1 @ sk_B @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,
    ( ( ( r1_binop_1 @ sk_B @ sk_D @ sk_F )
      | ~ ( m1_subset_1 @ sk_D @ sk_B ) )
   <= ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['206','212'])).

thf('214',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( r1_binop_1 @ sk_B @ sk_D @ sk_F )
   <= ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['2'])).

thf('217',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( r3_binop_1 @ X1 @ X2 @ X0 )
      | ( r1_binop_1 @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_E )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,
    ( ( ( r1_binop_1 @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_subset_1 @ sk_C @ sk_A ) )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['216','222'])).

thf('224',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( r1_binop_1 @ sk_A @ sk_C @ sk_E )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
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

thf('229',plain,(
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
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    v1_funct_2 @ sk_F @ ( k2_zfmisc_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
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
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,(
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
    inference('sup-',[status(thm)],['226','232'])).

thf('234',plain,(
    v1_funct_2 @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r1_binop_1 @ sk_A @ X1 @ sk_E )
      | ~ ( r1_binop_1 @ sk_B @ X0 @ sk_F )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ X1 @ X0 ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['233','234','235'])).

thf('237',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ sk_A )
        | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
        | ~ ( r1_binop_1 @ sk_B @ X0 @ sk_F )
        | ~ ( m1_subset_1 @ X0 @ sk_B )
        | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['225','236'])).

thf('238',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_A )
        | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
        | ~ ( r1_binop_1 @ sk_B @ X0 @ sk_F )
        | ~ ( m1_subset_1 @ X0 @ sk_B )
        | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_binop_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_D @ sk_B )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['215','239'])).

thf('241',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['242','243'])).

thf('245',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,
    ( ( r1_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['244','245'])).

thf('247',plain,(
    m1_subset_1 @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('248',plain,
    ( ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
      & ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['205','246','247'])).

thf('249',plain,
    ( ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
   <= ~ ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['106'])).

thf('250',plain,
    ( ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) )
    | ~ ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
    | ~ ( r3_binop_1 @ sk_B @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,
    ( ( r3_binop_1 @ sk_A @ sk_C @ sk_E )
    | ( r3_binop_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k1_domain_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_filter_1 @ sk_A @ sk_B @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['2'])).

thf('252',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','108','155','156','250','251'])).


%------------------------------------------------------------------------------
