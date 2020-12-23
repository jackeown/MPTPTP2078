%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ofmdk1BeU4

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 107 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  683 (1626 expanded)
%              Number of equality atoms :   35 (  62 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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

thf('3',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

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

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t63_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_tops_2])).

thf('16',plain,(
    ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X17 @ X19 )
       != X17 )
      | ~ ( v2_funct_1 @ X19 )
      | ( ( k2_tops_2 @ X18 @ X17 @ X19 )
        = ( k2_funct_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','32','33','38'])).

thf('40',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','40'])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['42','45','46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ofmdk1BeU4
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:32:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 70 iterations in 0.032s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(t55_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.50       ( ( v2_funct_1 @ A ) =>
% 0.22/0.50         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.22/0.50           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X5 : $i]:
% 0.22/0.50         (~ (v2_funct_1 @ X5)
% 0.22/0.50          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.22/0.50          | ~ (v1_funct_1 @ X5)
% 0.22/0.50          | ~ (v1_relat_1 @ X5))),
% 0.22/0.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.50  thf(dt_k2_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.50       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.22/0.50         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.50  thf(t61_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.50       ( ( v2_funct_1 @ A ) =>
% 0.22/0.50         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.22/0.50             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.22/0.50           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.22/0.50             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X6 : $i]:
% 0.22/0.50         (~ (v2_funct_1 @ X6)
% 0.22/0.50          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.22/0.50              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.22/0.50          | ~ (v1_funct_1 @ X6)
% 0.22/0.50          | ~ (v1_relat_1 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.22/0.50  thf(t48_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.22/0.50               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.22/0.50             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X3)
% 0.22/0.50          | ~ (v1_funct_1 @ X3)
% 0.22/0.50          | (v2_funct_1 @ X3)
% 0.22/0.50          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.22/0.50          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 0.22/0.50          | ~ (v1_funct_1 @ X4)
% 0.22/0.50          | ~ (v1_relat_1 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.22/0.50          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf(fc4_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.50  thf('6', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.22/0.50          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.22/0.50          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '8'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.22/0.50          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.50  thf(d3_struct_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X16 : $i]:
% 0.22/0.50         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.50  thf(t63_tops_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_struct_0 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( l1_struct_0 @ B ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                 ( m1_subset_1 @
% 0.22/0.50                   C @ 
% 0.22/0.50                   ( k1_zfmisc_1 @
% 0.22/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.50               ( ( ( ( k2_relset_1 @
% 0.22/0.50                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.22/0.50                     ( k2_struct_0 @ B ) ) & 
% 0.22/0.50                   ( v2_funct_1 @ C ) ) =>
% 0.22/0.50                 ( v2_funct_1 @
% 0.22/0.50                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( l1_struct_0 @ A ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( l1_struct_0 @ B ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.50                    ( v1_funct_2 @
% 0.22/0.50                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                    ( m1_subset_1 @
% 0.22/0.50                      C @ 
% 0.22/0.50                      ( k1_zfmisc_1 @
% 0.22/0.50                        ( k2_zfmisc_1 @
% 0.22/0.50                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.50                  ( ( ( ( k2_relset_1 @
% 0.22/0.50                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.22/0.50                        ( k2_struct_0 @ B ) ) & 
% 0.22/0.50                      ( v2_funct_1 @ C ) ) =>
% 0.22/0.50                    ( v2_funct_1 @
% 0.22/0.50                      ( k2_tops_2 @
% 0.22/0.50                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t63_tops_2])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (~ (v2_funct_1 @ 
% 0.22/0.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      ((~ (v2_funct_1 @ 
% 0.22/0.50           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.22/0.50        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (~ (v2_funct_1 @ 
% 0.22/0.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X16 : $i]:
% 0.22/0.50         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (((m1_subset_1 @ sk_C @ 
% 0.22/0.50         (k1_zfmisc_1 @ 
% 0.22/0.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.22/0.50        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.50      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf(d4_tops_2, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.50       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.22/0.50         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.50         (((k2_relset_1 @ X18 @ X17 @ X19) != (X17))
% 0.22/0.50          | ~ (v2_funct_1 @ X19)
% 0.22/0.50          | ((k2_tops_2 @ X18 @ X17 @ X19) = (k2_funct_1 @ X19))
% 0.22/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.22/0.50          | ~ (v1_funct_2 @ X19 @ X18 @ X17)
% 0.22/0.50          | ~ (v1_funct_1 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((~ (v1_funct_1 @ sk_C)
% 0.22/0.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.22/0.50        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.50            = (k2_funct_1 @ sk_C))
% 0.22/0.50        | ~ (v2_funct_1 @ sk_C)
% 0.22/0.50        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.50            != (k2_struct_0 @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X16 : $i]:
% 0.22/0.50         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.22/0.50        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.50      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('33', plain, ((v2_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X16 : $i]:
% 0.22/0.50         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.22/0.50         = (k2_struct_0 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.50          = (k2_struct_0 @ sk_B))
% 0.22/0.50        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.50      inference('sup+', [status(thm)], ['34', '35'])).
% 0.22/0.50  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.50         = (k2_struct_0 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.50          = (k2_funct_1 @ sk_C))
% 0.22/0.50        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['26', '27', '32', '33', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.50         = (k2_funct_1 @ sk_C))),
% 0.22/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.50  thf('41', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['19', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '41'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc1_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( v1_relat_1 @ C ) ))).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         ((v1_relat_1 @ X7)
% 0.22/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.50  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('48', plain, ($false),
% 0.22/0.50      inference('demod', [status(thm)], ['42', '45', '46', '47'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
