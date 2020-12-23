%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9NjH9PwNkp

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:40 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 443 expanded)
%              Number of leaves         :   29 ( 147 expanded)
%              Depth                    :   20
%              Number of atoms          : 1379 (5888 expanded)
%              Number of equality atoms :  104 ( 585 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t64_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( ( k2_relat_1 @ B )
                  = ( k1_relat_1 @ A ) )
                & ( ( k5_relat_1 @ B @ A )
                  = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_1])).

thf('0',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
       != ( k6_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('14',plain,(
    ! [X14: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
        = X14 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X13: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','18','19'])).

thf('21',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','20'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('23',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ( v2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('30',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('33',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','20'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','38'])).

thf('40',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('43',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k2_funct_1 @ sk_A ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k2_funct_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','20'])).

thf('53',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_funct_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','53','54','55','56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['31','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('64',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('65',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('66',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('67',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( ( k2_funct_1 @ sk_A )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['62','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k2_funct_1 @ sk_A )
      = sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['30','81'])).

thf('83',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('84',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('85',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('86',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('89',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('95',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['86','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('100',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','103','104','105','106'])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['85','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
      = ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','119'])).

thf('121',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','18','19'])).

thf('123',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( sk_A
    = ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','125','126'])).

thf('128',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X17 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('129',plain,
    ( ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) )
    | ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('132',plain,(
    ! [X13: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','18','19'])).

thf('134',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('135',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133','134','135','136'])).

thf('138',plain,(
    v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['82','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9NjH9PwNkp
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 145 iterations in 0.140s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.60  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.41/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.41/0.60  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(t64_funct_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.60           ( ( ( v2_funct_1 @ A ) & 
% 0.41/0.60               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.41/0.60               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.41/0.60             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.60              ( ( ( v2_funct_1 @ A ) & 
% 0.41/0.60                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.41/0.60                  ( ( k5_relat_1 @ B @ A ) =
% 0.41/0.60                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.41/0.60                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_k2_subset_1, axiom,
% 0.41/0.60    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.41/0.60  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.41/0.60  thf('2', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.41/0.60  thf('3', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.41/0.60      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf(t3_subset, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i]:
% 0.41/0.60         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.60  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.41/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf('6', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t46_relat_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( v1_relat_1 @ B ) =>
% 0.41/0.60           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.60             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X5)
% 0.41/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) = (k1_relat_1 @ X6))
% 0.41/0.60          | ~ (r1_tarski @ (k2_relat_1 @ X6) @ (k1_relat_1 @ X5))
% 0.41/0.60          | ~ (v1_relat_1 @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.60  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['8', '9'])).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      ((((k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)) = (k1_relat_1 @ sk_B))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '10'])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t34_funct_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.60       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.41/0.60         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X14 : $i, X15 : $i]:
% 0.41/0.60         (((X15) != (k6_relat_1 @ X14))
% 0.41/0.60          | ((k1_relat_1 @ X15) = (X14))
% 0.41/0.60          | ~ (v1_funct_1 @ X15)
% 0.41/0.60          | ~ (v1_relat_1 @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X14 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ (k6_relat_1 @ X14))
% 0.41/0.60          | ~ (v1_funct_1 @ (k6_relat_1 @ X14))
% 0.41/0.60          | ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.41/0.60  thf(fc3_funct_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.41/0.60       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.41/0.60  thf('15', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('16', plain, (![X13 : $i]: (v1_funct_1 @ (k6_relat_1 @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('17', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.41/0.60      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (((k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['12', '17'])).
% 0.41/0.60  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('20', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['11', '18', '19'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '20'])).
% 0.41/0.60  thf(t48_funct_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.60           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.41/0.60               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.41/0.60             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X17)
% 0.41/0.60          | ~ (v1_funct_1 @ X17)
% 0.41/0.60          | (v2_funct_1 @ X17)
% 0.41/0.60          | ((k2_relat_1 @ X17) != (k1_relat_1 @ X18))
% 0.41/0.60          | ~ (v2_funct_1 @ (k5_relat_1 @ X17 @ X18))
% 0.41/0.60          | ~ (v1_funct_1 @ X18)
% 0.41/0.60          | ~ (v1_relat_1 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      ((~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_A)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_A)
% 0.41/0.60        | ((k2_relat_1 @ sk_B) != (k1_relat_1 @ sk_A))
% 0.41/0.60        | (v2_funct_1 @ sk_B)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_B)
% 0.41/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('25', plain, ((v1_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('26', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      ((~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.41/0.60        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B))
% 0.41/0.60        | (v2_funct_1 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '28'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (((v2_funct_1 @ sk_B)
% 0.41/0.60        | ~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['29'])).
% 0.41/0.60  thf(dt_k2_funct_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.60       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.41/0.60         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X11 : $i]:
% 0.41/0.60         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.41/0.60          | ~ (v1_funct_1 @ X11)
% 0.41/0.60          | ~ (v1_relat_1 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.41/0.60  thf(t61_funct_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.60       ( ( v2_funct_1 @ A ) =>
% 0.41/0.60         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.41/0.60             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.41/0.60           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.41/0.60             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (![X20 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X20)
% 0.41/0.60          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 0.41/0.60              = (k6_relat_1 @ (k1_relat_1 @ X20)))
% 0.41/0.60          | ~ (v1_funct_1 @ X20)
% 0.41/0.60          | ~ (v1_relat_1 @ X20))),
% 0.41/0.60      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '20'])).
% 0.41/0.60  thf(t55_relat_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( v1_relat_1 @ B ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( v1_relat_1 @ C ) =>
% 0.41/0.60               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.41/0.60                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X7)
% 0.41/0.60          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.41/0.60              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.41/0.60          | ~ (v1_relat_1 @ X9)
% 0.41/0.60          | ~ (v1_relat_1 @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.41/0.60            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))
% 0.41/0.60          | ~ (v1_relat_1 @ sk_B)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['33', '34'])).
% 0.41/0.60  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.41/0.60            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))
% 0.41/0.60          | ~ (v1_relat_1 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ (k2_funct_1 @ sk_A))
% 0.41/0.60          = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_A)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_A)
% 0.41/0.60        | ~ (v2_funct_1 @ sk_A)
% 0.41/0.60        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['32', '38'])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      (![X11 : $i]:
% 0.41/0.60         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.41/0.60          | ~ (v1_funct_1 @ X11)
% 0.41/0.60          | ~ (v1_relat_1 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.41/0.60  thf(t55_funct_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.60       ( ( v2_funct_1 @ A ) =>
% 0.41/0.60         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.41/0.60           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X19 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X19)
% 0.41/0.60          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 0.41/0.60          | ~ (v1_funct_1 @ X19)
% 0.41/0.60          | ~ (v1_relat_1 @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.41/0.60  thf(t78_relat_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ A ) =>
% 0.41/0.60       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      (![X10 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 0.41/0.60          | ~ (v1_relat_1 @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.41/0.60            = (k2_funct_1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v2_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['42', '43'])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v2_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.41/0.60              = (k2_funct_1 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '44'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.41/0.60            = (k2_funct_1 @ X0))
% 0.41/0.60          | ~ (v2_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['45'])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      ((((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ (k2_funct_1 @ sk_A))
% 0.41/0.60          = (k2_funct_1 @ sk_A))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_A)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_A)
% 0.41/0.60        | ~ (v2_funct_1 @ sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['40', '46'])).
% 0.41/0.60  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('49', plain, ((v1_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('50', plain, ((v2_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ (k2_funct_1 @ sk_A))
% 0.41/0.60         = (k2_funct_1 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '20'])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ (k2_funct_1 @ sk_A))
% 0.41/0.60         = (k2_funct_1 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['51', '52'])).
% 0.41/0.60  thf('54', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('56', plain, ((v1_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('57', plain, ((v2_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      ((((k2_funct_1 @ sk_A)
% 0.41/0.60          = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))
% 0.41/0.60        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['39', '53', '54', '55', '56', '57'])).
% 0.41/0.60  thf('59', plain,
% 0.41/0.60      ((~ (v1_relat_1 @ sk_A)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_A)
% 0.41/0.60        | ((k2_funct_1 @ sk_A)
% 0.41/0.60            = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['31', '58'])).
% 0.41/0.60  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('61', plain, ((v1_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      (((k2_funct_1 @ sk_A)
% 0.41/0.60         = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      (![X20 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X20)
% 0.41/0.60          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 0.41/0.60              = (k6_relat_1 @ (k2_relat_1 @ X20)))
% 0.41/0.60          | ~ (v1_funct_1 @ X20)
% 0.41/0.60          | ~ (v1_relat_1 @ X20))),
% 0.41/0.60      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      (![X11 : $i]:
% 0.41/0.60         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.41/0.60          | ~ (v1_funct_1 @ X11)
% 0.41/0.60          | ~ (v1_relat_1 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.41/0.60  thf('65', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X7)
% 0.41/0.60          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.41/0.60              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.41/0.60          | ~ (v1_relat_1 @ X9)
% 0.41/0.60          | ~ (v1_relat_1 @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      (![X20 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X20)
% 0.41/0.60          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 0.41/0.60              = (k6_relat_1 @ (k1_relat_1 @ X20)))
% 0.41/0.60          | ~ (v1_funct_1 @ X20)
% 0.41/0.60          | ~ (v1_relat_1 @ X20))),
% 0.41/0.60      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      (![X10 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 0.41/0.60          | ~ (v1_relat_1 @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.41/0.60  thf('68', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X0) = (X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v2_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['66', '67'])).
% 0.41/0.60  thf('69', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X0) = (X0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['68'])).
% 0.41/0.60  thf('70', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)) = (X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v2_funct_1 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['65', '69'])).
% 0.41/0.60  thf('71', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ((k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)) = (X0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['70'])).
% 0.41/0.60  thf('72', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ((k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)) = (X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v2_funct_1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['64', '71'])).
% 0.41/0.60  thf('73', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X0)
% 0.41/0.60          | ((k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)) = (X0))
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['72'])).
% 0.41/0.60  thf('74', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v2_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v2_funct_1 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['63', '73'])).
% 0.41/0.60  thf('75', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['74'])).
% 0.41/0.60  thf('76', plain,
% 0.41/0.60      ((((k2_funct_1 @ sk_A) = (sk_B))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_B)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_B)
% 0.41/0.60        | ~ (v2_funct_1 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['62', '75'])).
% 0.41/0.60  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('78', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('79', plain, ((((k2_funct_1 @ sk_A) = (sk_B)) | ~ (v2_funct_1 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.41/0.60  thf('80', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('81', plain, (~ (v2_funct_1 @ sk_B)),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 0.41/0.60  thf('82', plain, (~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.41/0.60      inference('clc', [status(thm)], ['30', '81'])).
% 0.41/0.60  thf('83', plain,
% 0.41/0.60      (![X20 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X20)
% 0.41/0.60          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 0.41/0.60              = (k6_relat_1 @ (k2_relat_1 @ X20)))
% 0.41/0.60          | ~ (v1_funct_1 @ X20)
% 0.41/0.60          | ~ (v1_relat_1 @ X20))),
% 0.41/0.60      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.41/0.60  thf('84', plain,
% 0.41/0.60      (![X11 : $i]:
% 0.41/0.60         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.41/0.60          | ~ (v1_funct_1 @ X11)
% 0.41/0.60          | ~ (v1_relat_1 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.41/0.60  thf('85', plain,
% 0.41/0.60      (![X11 : $i]:
% 0.41/0.60         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.41/0.60          | ~ (v1_funct_1 @ X11)
% 0.41/0.60          | ~ (v1_relat_1 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.41/0.60  thf('86', plain,
% 0.41/0.60      (![X20 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X20)
% 0.41/0.60          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 0.41/0.60              = (k6_relat_1 @ (k1_relat_1 @ X20)))
% 0.41/0.60          | ~ (v1_funct_1 @ X20)
% 0.41/0.60          | ~ (v1_relat_1 @ X20))),
% 0.41/0.60      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.41/0.60  thf('87', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('88', plain,
% 0.41/0.60      (![X10 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 0.41/0.60          | ~ (v1_relat_1 @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.41/0.60  thf('89', plain,
% 0.41/0.60      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['87', '88'])).
% 0.41/0.60  thf('90', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('91', plain,
% 0.41/0.60      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['89', '90'])).
% 0.41/0.60  thf('92', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X7)
% 0.41/0.60          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.41/0.60              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.41/0.60          | ~ (v1_relat_1 @ X9)
% 0.41/0.60          | ~ (v1_relat_1 @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.41/0.60  thf('93', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ sk_A @ X0)
% 0.41/0.60            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.41/0.60               (k5_relat_1 @ sk_A @ X0)))
% 0.41/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['91', '92'])).
% 0.41/0.60  thf('94', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('95', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('96', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ sk_A @ X0)
% 0.41/0.60            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.41/0.60               (k5_relat_1 @ sk_A @ X0)))
% 0.41/0.60          | ~ (v1_relat_1 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.41/0.60  thf('97', plain,
% 0.41/0.60      ((((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 0.41/0.60          = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.41/0.60             (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_A)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_A)
% 0.41/0.60        | ~ (v2_funct_1 @ sk_A)
% 0.41/0.60        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['86', '96'])).
% 0.41/0.60  thf('98', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('99', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.41/0.60      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.41/0.60  thf('100', plain,
% 0.41/0.60      (![X10 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 0.41/0.60          | ~ (v1_relat_1 @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.41/0.60  thf('101', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.41/0.60            = (k6_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['99', '100'])).
% 0.41/0.60  thf('102', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('103', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.41/0.60           = (k6_relat_1 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['101', '102'])).
% 0.41/0.60  thf('104', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('105', plain, ((v1_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('106', plain, ((v2_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('107', plain,
% 0.41/0.60      ((((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 0.41/0.60          = (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.41/0.60        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)],
% 0.41/0.60                ['97', '98', '103', '104', '105', '106'])).
% 0.41/0.60  thf('108', plain,
% 0.41/0.60      ((~ (v1_relat_1 @ sk_A)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_A)
% 0.41/0.60        | ((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 0.41/0.60            = (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['85', '107'])).
% 0.41/0.60  thf('109', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('110', plain, ((v1_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('111', plain,
% 0.41/0.60      (((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 0.41/0.60         = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.41/0.60  thf('112', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X7)
% 0.41/0.60          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.41/0.60              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.41/0.60          | ~ (v1_relat_1 @ X9)
% 0.41/0.60          | ~ (v1_relat_1 @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.41/0.60  thf('113', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)
% 0.41/0.60            = (k5_relat_1 @ sk_A @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)))
% 0.41/0.60          | ~ (v1_relat_1 @ sk_A)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['111', '112'])).
% 0.41/0.60  thf('114', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('115', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)
% 0.41/0.60            = (k5_relat_1 @ sk_A @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['113', '114'])).
% 0.41/0.60  thf('116', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ sk_A)
% 0.41/0.60          | ~ (v1_funct_1 @ sk_A)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)
% 0.41/0.60              = (k5_relat_1 @ sk_A @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['84', '115'])).
% 0.41/0.60  thf('117', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('118', plain, ((v1_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('119', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X0)
% 0.41/0.60          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)
% 0.41/0.60              = (k5_relat_1 @ sk_A @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0))))),
% 0.41/0.60      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.41/0.60  thf('120', plain,
% 0.41/0.60      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A)
% 0.41/0.60          = (k5_relat_1 @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_A))))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_A)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_A)
% 0.41/0.60        | ~ (v2_funct_1 @ sk_A)
% 0.41/0.60        | ~ (v1_relat_1 @ sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['83', '119'])).
% 0.41/0.60  thf('121', plain,
% 0.41/0.60      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['89', '90'])).
% 0.41/0.60  thf('122', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['11', '18', '19'])).
% 0.41/0.60  thf('123', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('124', plain, ((v1_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('125', plain, ((v2_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('126', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('127', plain,
% 0.41/0.60      (((sk_A) = (k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)],
% 0.41/0.60                ['120', '121', '122', '123', '124', '125', '126'])).
% 0.41/0.60  thf('128', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X17)
% 0.41/0.60          | ~ (v1_funct_1 @ X17)
% 0.41/0.60          | (v2_funct_1 @ X18)
% 0.41/0.60          | ((k2_relat_1 @ X17) != (k1_relat_1 @ X18))
% 0.41/0.60          | ~ (v2_funct_1 @ (k5_relat_1 @ X17 @ X18))
% 0.41/0.60          | ~ (v1_funct_1 @ X18)
% 0.41/0.60          | ~ (v1_relat_1 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.41/0.60  thf('129', plain,
% 0.41/0.60      ((~ (v2_funct_1 @ sk_A)
% 0.41/0.60        | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.41/0.60        | ~ (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.41/0.60        | ((k2_relat_1 @ sk_A)
% 0.41/0.60            != (k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))
% 0.41/0.60        | (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.41/0.60        | ~ (v1_funct_1 @ sk_A)
% 0.41/0.60        | ~ (v1_relat_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['127', '128'])).
% 0.41/0.60  thf('130', plain, ((v2_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('131', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('132', plain, (![X13 : $i]: (v1_funct_1 @ (k6_relat_1 @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('133', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['11', '18', '19'])).
% 0.41/0.60  thf('134', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.41/0.60      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.41/0.60  thf('135', plain, ((v1_funct_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('136', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('137', plain,
% 0.41/0.60      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.41/0.60        | (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)],
% 0.41/0.60                ['129', '130', '131', '132', '133', '134', '135', '136'])).
% 0.41/0.60  thf('138', plain, ((v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['137'])).
% 0.41/0.60  thf('139', plain, ($false), inference('demod', [status(thm)], ['82', '138'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
