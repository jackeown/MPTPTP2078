%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mKW0kWfeTu

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:50 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  243 (3711 expanded)
%              Number of leaves         :   42 (1075 expanded)
%              Depth                    :   31
%              Number of atoms          : 2396 (96408 expanded)
%              Number of equality atoms :  148 (4898 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('5',plain,(
    ! [X3: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('8',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('9',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('32',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('65',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','69'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('71',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('74',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('77',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('78',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','75','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','75','78'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('82',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','69'])).

thf('95',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('102',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('103',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['92','104'])).

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

thf('106',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_tops_2 @ X29 @ X28 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('107',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('110',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','75','78'])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('114',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('120',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','75','78'])).

thf('122',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['107','108','111','112','122'])).

thf('124',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['92','104'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('126',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relset_1 @ X25 @ X24 @ X23 )
       != X24 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('127',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('130',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131'])).

thf('133',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('135',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100','103'])).

thf('137',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','44','79','80','81','124','135','136'])).

thf('138',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('139',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('140',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('142',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('143',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('144',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('146',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != X21 )
      | ( v1_partfun1 @ X22 @ X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('147',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v4_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
      | ( v1_partfun1 @ X22 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['145','147'])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['144','148'])).

thf('150',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('151',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('152',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','152','153','154','155'])).

thf('157',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['141','156'])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('161',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('163',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('165',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('166',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['140','166'])).

thf('168',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['123'])).

thf('169',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('170',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('171',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['32'])).

thf('173',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['170','175'])).

thf('177',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['169','178'])).

thf('180',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('183',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','75','78'])).

thf('184',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100','103'])).

thf('185',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('186',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('187',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['181','182','183','184','185','186'])).

thf('188',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['168','187'])).

thf('189',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['167','188'])).

thf('190',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['32'])).

thf('192',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['190','191'])).

thf('193',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['137','192'])).

thf('194',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('199',plain,(
    $false ),
    inference(simplify,[status(thm)],['198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mKW0kWfeTu
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 361 iterations in 0.158s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.42/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.42/0.61  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.42/0.61  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.42/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.42/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(dt_k2_funct_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.61       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.42/0.61         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (![X2 : $i]:
% 0.42/0.61         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | ~ (v1_relat_1 @ X2))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X2 : $i]:
% 0.42/0.61         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | ~ (v1_relat_1 @ X2))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.42/0.61  thf(fc6_funct_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.42/0.61       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.42/0.61         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.42/0.61         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X3 : $i]:
% 0.42/0.61         ((v2_funct_1 @ (k2_funct_1 @ X3))
% 0.42/0.61          | ~ (v2_funct_1 @ X3)
% 0.42/0.61          | ~ (v1_funct_1 @ X3)
% 0.42/0.61          | ~ (v1_relat_1 @ X3))),
% 0.42/0.61      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.42/0.61  thf(t65_funct_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.61       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X5 : $i]:
% 0.42/0.61         (~ (v2_funct_1 @ X5)
% 0.42/0.61          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.42/0.61          | ~ (v1_funct_1 @ X5)
% 0.42/0.61          | ~ (v1_relat_1 @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.42/0.61  thf(t61_funct_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.61       ( ( v2_funct_1 @ A ) =>
% 0.42/0.61         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.42/0.61             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.42/0.61           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.42/0.61             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (![X4 : $i]:
% 0.42/0.61         (~ (v2_funct_1 @ X4)
% 0.42/0.61          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 0.42/0.61              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.42/0.61          | ~ (v1_funct_1 @ X4)
% 0.42/0.61          | ~ (v1_relat_1 @ X4))),
% 0.42/0.61      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X3 : $i]:
% 0.42/0.61         ((v2_funct_1 @ (k2_funct_1 @ X3))
% 0.42/0.61          | ~ (v2_funct_1 @ X3)
% 0.42/0.61          | ~ (v1_funct_1 @ X3)
% 0.42/0.61          | ~ (v1_relat_1 @ X3))),
% 0.42/0.61      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X2 : $i]:
% 0.42/0.61         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | ~ (v1_relat_1 @ X2))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X2 : $i]:
% 0.42/0.61         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | ~ (v1_relat_1 @ X2))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X5 : $i]:
% 0.42/0.61         (~ (v2_funct_1 @ X5)
% 0.42/0.61          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.42/0.61          | ~ (v1_funct_1 @ X5)
% 0.42/0.61          | ~ (v1_relat_1 @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X4 : $i]:
% 0.42/0.61         (~ (v2_funct_1 @ X4)
% 0.42/0.61          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.42/0.61              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.42/0.61          | ~ (v1_funct_1 @ X4)
% 0.42/0.61          | ~ (v1_relat_1 @ X4))),
% 0.42/0.61      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.42/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['8', '9'])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.42/0.61              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['7', '10'])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.42/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['11'])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.42/0.61              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['6', '12'])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.42/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['13'])).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.42/0.61              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '14'])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.42/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.42/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['4', '16'])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.42/0.61              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.42/0.61  thf(t71_relat_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.42/0.61       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.42/0.61  thf('19', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.42/0.61            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['18', '19'])).
% 0.42/0.61  thf('21', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['3', '22'])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '23'])).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '25'])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['26'])).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '27'])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['28'])).
% 0.42/0.61  thf(d3_struct_0, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (![X26 : $i]:
% 0.42/0.61         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      (![X26 : $i]:
% 0.42/0.61         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.61  thf(t62_tops_2, conjecture,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( l1_struct_0 @ A ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.42/0.61                 ( m1_subset_1 @
% 0.42/0.61                   C @ 
% 0.42/0.61                   ( k1_zfmisc_1 @
% 0.42/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.42/0.61               ( ( ( ( k2_relset_1 @
% 0.42/0.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.42/0.61                     ( k2_struct_0 @ B ) ) & 
% 0.42/0.61                   ( v2_funct_1 @ C ) ) =>
% 0.42/0.61                 ( ( ( k1_relset_1 @
% 0.42/0.61                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.42/0.61                       ( k2_tops_2 @
% 0.42/0.61                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.42/0.61                     ( k2_struct_0 @ B ) ) & 
% 0.42/0.61                   ( ( k2_relset_1 @
% 0.42/0.61                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.42/0.61                       ( k2_tops_2 @
% 0.42/0.61                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.42/0.61                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]:
% 0.42/0.61        ( ( l1_struct_0 @ A ) =>
% 0.42/0.61          ( ![B:$i]:
% 0.42/0.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.42/0.61              ( ![C:$i]:
% 0.42/0.61                ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.61                    ( v1_funct_2 @
% 0.42/0.61                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.42/0.61                    ( m1_subset_1 @
% 0.42/0.61                      C @ 
% 0.42/0.61                      ( k1_zfmisc_1 @
% 0.42/0.61                        ( k2_zfmisc_1 @
% 0.42/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.42/0.61                  ( ( ( ( k2_relset_1 @
% 0.42/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.42/0.61                        ( k2_struct_0 @ B ) ) & 
% 0.42/0.61                      ( v2_funct_1 @ C ) ) =>
% 0.42/0.61                    ( ( ( k1_relset_1 @
% 0.42/0.61                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.42/0.61                          ( k2_tops_2 @
% 0.42/0.61                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.42/0.61                        ( k2_struct_0 @ B ) ) & 
% 0.42/0.61                      ( ( k2_relset_1 @
% 0.42/0.61                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.42/0.61                          ( k2_tops_2 @
% 0.42/0.61                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.42/0.61                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          != (k2_struct_0 @ sk_B))
% 0.42/0.61        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61            != (k2_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('33', plain,
% 0.42/0.61      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          != (k2_struct_0 @ sk_A)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_A))))),
% 0.42/0.61      inference('split', [status(esa)], ['32'])).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61           != (k2_struct_0 @ sk_A))
% 0.42/0.61         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['31', '33'])).
% 0.42/0.61  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          != (k2_struct_0 @ sk_A)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_A))))),
% 0.42/0.61      inference('demod', [status(thm)], ['34', '35'])).
% 0.42/0.61  thf('37', plain,
% 0.42/0.61      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61           != (k2_struct_0 @ sk_A))
% 0.42/0.61         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['30', '36'])).
% 0.42/0.61  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          != (k2_struct_0 @ sk_A)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_A))))),
% 0.42/0.61      inference('demod', [status(thm)], ['37', '38'])).
% 0.42/0.61  thf('40', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k2_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.42/0.61  thf('41', plain,
% 0.42/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.61         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.42/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.61  thf('42', plain,
% 0.42/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.42/0.61         = (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.42/0.61         = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('44', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      (![X26 : $i]:
% 0.42/0.61         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      (((m1_subset_1 @ sk_C @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.42/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['45', '46'])).
% 0.42/0.61  thf('48', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('49', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.42/0.61  thf('50', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('51', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.42/0.61      inference('demod', [status(thm)], ['49', '50'])).
% 0.42/0.61  thf(cc5_funct_2, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.61       ( ![C:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.42/0.61             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.42/0.61          | (v1_partfun1 @ X18 @ X19)
% 0.42/0.61          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.42/0.61          | ~ (v1_funct_1 @ X18)
% 0.42/0.61          | (v1_xboole_0 @ X20))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.42/0.61  thf('53', plain,
% 0.42/0.61      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.42/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.42/0.61        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['51', '52'])).
% 0.42/0.61  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('55', plain,
% 0.42/0.61      (![X26 : $i]:
% 0.42/0.61         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.61  thf('56', plain,
% 0.42/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('57', plain,
% 0.42/0.61      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.42/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['55', '56'])).
% 0.42/0.61  thf('58', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('59', plain,
% 0.42/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('demod', [status(thm)], ['57', '58'])).
% 0.42/0.61  thf('60', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('61', plain,
% 0.42/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['59', '60'])).
% 0.42/0.61  thf('62', plain,
% 0.42/0.61      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.42/0.61        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('demod', [status(thm)], ['53', '54', '61'])).
% 0.42/0.61  thf('63', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf(fc5_struct_0, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.42/0.61       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.42/0.61  thf('64', plain,
% 0.42/0.61      (![X27 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ (k2_struct_0 @ X27))
% 0.42/0.61          | ~ (l1_struct_0 @ X27)
% 0.42/0.61          | (v2_struct_0 @ X27))),
% 0.42/0.61      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.42/0.61  thf('65', plain,
% 0.42/0.61      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.42/0.61        | (v2_struct_0 @ sk_B)
% 0.42/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.42/0.61  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('67', plain,
% 0.42/0.61      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.42/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.42/0.61  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('69', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('clc', [status(thm)], ['67', '68'])).
% 0.42/0.61  thf('70', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('clc', [status(thm)], ['62', '69'])).
% 0.42/0.61  thf(d4_partfun1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.42/0.61       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.42/0.61  thf('71', plain,
% 0.42/0.61      (![X21 : $i, X22 : $i]:
% 0.42/0.61         (~ (v1_partfun1 @ X22 @ X21)
% 0.42/0.61          | ((k1_relat_1 @ X22) = (X21))
% 0.42/0.61          | ~ (v4_relat_1 @ X22 @ X21)
% 0.42/0.61          | ~ (v1_relat_1 @ X22))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.42/0.61  thf('72', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.42/0.61        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.42/0.61        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.42/0.61  thf('73', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(cc1_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( v1_relat_1 @ C ) ))).
% 0.42/0.61  thf('74', plain,
% 0.42/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.61         ((v1_relat_1 @ X6)
% 0.42/0.61          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.61  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.42/0.61  thf('76', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(cc2_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.61  thf('77', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         ((v4_relat_1 @ X9 @ X10)
% 0.42/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.61  thf('78', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['76', '77'])).
% 0.42/0.61  thf('79', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['72', '75', '78'])).
% 0.42/0.61  thf('80', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['72', '75', '78'])).
% 0.42/0.61  thf('81', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('82', plain,
% 0.42/0.61      (![X26 : $i]:
% 0.42/0.61         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.61  thf('83', plain,
% 0.42/0.61      (![X26 : $i]:
% 0.42/0.61         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.61  thf('84', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('85', plain,
% 0.42/0.61      (((m1_subset_1 @ sk_C @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.42/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.61      inference('sup+', [status(thm)], ['83', '84'])).
% 0.42/0.61  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('87', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)], ['85', '86'])).
% 0.42/0.61  thf('88', plain,
% 0.42/0.61      (((m1_subset_1 @ sk_C @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.42/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['82', '87'])).
% 0.42/0.61  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('90', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)], ['88', '89'])).
% 0.42/0.61  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('92', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.42/0.61      inference('demod', [status(thm)], ['90', '91'])).
% 0.42/0.61  thf('93', plain,
% 0.42/0.61      (![X26 : $i]:
% 0.42/0.61         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.61  thf('94', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('clc', [status(thm)], ['62', '69'])).
% 0.42/0.61  thf('95', plain,
% 0.42/0.61      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.61      inference('sup+', [status(thm)], ['93', '94'])).
% 0.42/0.61  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('97', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['95', '96'])).
% 0.42/0.61  thf('98', plain,
% 0.42/0.61      (![X21 : $i, X22 : $i]:
% 0.42/0.61         (~ (v1_partfun1 @ X22 @ X21)
% 0.42/0.61          | ((k1_relat_1 @ X22) = (X21))
% 0.42/0.61          | ~ (v4_relat_1 @ X22 @ X21)
% 0.42/0.61          | ~ (v1_relat_1 @ X22))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.42/0.61  thf('99', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.42/0.61        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.42/0.61        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.42/0.61  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.42/0.61  thf('101', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)], ['85', '86'])).
% 0.42/0.61  thf('102', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         ((v4_relat_1 @ X9 @ X10)
% 0.42/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.61  thf('103', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['101', '102'])).
% 0.42/0.61  thf('104', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['99', '100', '103'])).
% 0.42/0.61  thf('105', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.42/0.61      inference('demod', [status(thm)], ['92', '104'])).
% 0.42/0.61  thf(d4_tops_2, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.61       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.42/0.61         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.42/0.61  thf('106', plain,
% 0.42/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.42/0.61         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.42/0.61          | ~ (v2_funct_1 @ X30)
% 0.42/0.61          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.42/0.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.42/0.61          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.42/0.61          | ~ (v1_funct_1 @ X30))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.42/0.61  thf('107', plain,
% 0.42/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.42/0.61        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.42/0.61        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.42/0.61            = (k2_funct_1 @ sk_C))
% 0.42/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.42/0.61        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.42/0.61            != (k2_relat_1 @ sk_C)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['105', '106'])).
% 0.42/0.61  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('109', plain,
% 0.42/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['59', '60'])).
% 0.42/0.61  thf('110', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['72', '75', '78'])).
% 0.42/0.61  thf('111', plain,
% 0.42/0.61      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['109', '110'])).
% 0.42/0.61  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('113', plain,
% 0.42/0.61      (![X26 : $i]:
% 0.42/0.61         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.61  thf('114', plain,
% 0.42/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.42/0.61         = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('115', plain,
% 0.42/0.61      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.42/0.61          = (k2_struct_0 @ sk_B))
% 0.42/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['113', '114'])).
% 0.42/0.61  thf('116', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('117', plain,
% 0.42/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.42/0.61         = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('demod', [status(thm)], ['115', '116'])).
% 0.42/0.61  thf('118', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('119', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('120', plain,
% 0.42/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.42/0.61         = (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.42/0.61  thf('121', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['72', '75', '78'])).
% 0.42/0.61  thf('122', plain,
% 0.42/0.61      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.42/0.61         = (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['120', '121'])).
% 0.42/0.61  thf('123', plain,
% 0.42/0.61      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.42/0.61          = (k2_funct_1 @ sk_C))
% 0.42/0.61        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.42/0.61      inference('demod', [status(thm)], ['107', '108', '111', '112', '122'])).
% 0.42/0.61  thf('124', plain,
% 0.42/0.61      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.42/0.61         = (k2_funct_1 @ sk_C))),
% 0.42/0.61      inference('simplify', [status(thm)], ['123'])).
% 0.42/0.61  thf('125', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.42/0.61      inference('demod', [status(thm)], ['92', '104'])).
% 0.42/0.61  thf(t31_funct_2, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.61       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.42/0.61         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.42/0.61           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.42/0.61           ( m1_subset_1 @
% 0.42/0.61             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.42/0.61  thf('126', plain,
% 0.42/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.42/0.61         (~ (v2_funct_1 @ X23)
% 0.42/0.61          | ((k2_relset_1 @ X25 @ X24 @ X23) != (X24))
% 0.42/0.61          | (m1_subset_1 @ (k2_funct_1 @ X23) @ 
% 0.42/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.42/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.42/0.61          | ~ (v1_funct_2 @ X23 @ X25 @ X24)
% 0.42/0.61          | ~ (v1_funct_1 @ X23))),
% 0.42/0.61      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.42/0.61  thf('127', plain,
% 0.42/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.42/0.61        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.42/0.61        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.42/0.61           (k1_zfmisc_1 @ 
% 0.42/0.61            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.42/0.61        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.42/0.61            != (k2_relat_1 @ sk_C))
% 0.42/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['125', '126'])).
% 0.42/0.61  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('129', plain,
% 0.42/0.61      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['109', '110'])).
% 0.42/0.61  thf('130', plain,
% 0.42/0.61      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.42/0.61         = (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['120', '121'])).
% 0.42/0.61  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('132', plain,
% 0.42/0.61      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.42/0.61        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.42/0.61      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 0.42/0.61  thf('133', plain,
% 0.42/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['132'])).
% 0.42/0.61  thf('134', plain,
% 0.42/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.61         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.42/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.61  thf('135', plain,
% 0.42/0.61      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.61         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['133', '134'])).
% 0.42/0.61  thf('136', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['99', '100', '103'])).
% 0.42/0.61  thf('137', plain,
% 0.42/0.61      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_A))))),
% 0.42/0.61      inference('demod', [status(thm)],
% 0.42/0.61                ['39', '44', '79', '80', '81', '124', '135', '136'])).
% 0.42/0.61  thf('138', plain,
% 0.42/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['132'])).
% 0.42/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.61  thf('139', plain,
% 0.42/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.61         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.42/0.61          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.61  thf('140', plain,
% 0.42/0.61      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.61         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['138', '139'])).
% 0.42/0.61  thf('141', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.61  thf('142', plain,
% 0.42/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['132'])).
% 0.42/0.61  thf('143', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         ((v4_relat_1 @ X9 @ X10)
% 0.42/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.61  thf('144', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['142', '143'])).
% 0.42/0.61  thf('145', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.61  thf('146', plain,
% 0.42/0.61      (![X21 : $i, X22 : $i]:
% 0.42/0.61         (((k1_relat_1 @ X22) != (X21))
% 0.42/0.61          | (v1_partfun1 @ X22 @ X21)
% 0.42/0.61          | ~ (v4_relat_1 @ X22 @ X21)
% 0.42/0.61          | ~ (v1_relat_1 @ X22))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.42/0.61  thf('147', plain,
% 0.42/0.61      (![X22 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X22)
% 0.42/0.61          | ~ (v4_relat_1 @ X22 @ (k1_relat_1 @ X22))
% 0.42/0.61          | (v1_partfun1 @ X22 @ (k1_relat_1 @ X22)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['146'])).
% 0.42/0.61  thf('148', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.42/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['145', '147'])).
% 0.42/0.61  thf('149', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.42/0.61        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 0.42/0.61           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.42/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['144', '148'])).
% 0.42/0.61  thf('150', plain,
% 0.42/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.42/0.61        (k1_zfmisc_1 @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['132'])).
% 0.42/0.61  thf('151', plain,
% 0.42/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.61         ((v1_relat_1 @ X6)
% 0.42/0.61          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.61  thf('152', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['150', '151'])).
% 0.42/0.61  thf('153', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.42/0.61  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('155', plain, ((v2_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('156', plain,
% 0.42/0.61      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.42/0.61      inference('demod', [status(thm)], ['149', '152', '153', '154', '155'])).
% 0.42/0.61  thf('157', plain,
% 0.42/0.61      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.42/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.42/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.42/0.61      inference('sup+', [status(thm)], ['141', '156'])).
% 0.42/0.61  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.42/0.61  thf('161', plain,
% 0.42/0.61      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 0.42/0.61  thf('162', plain,
% 0.42/0.61      (![X21 : $i, X22 : $i]:
% 0.42/0.61         (~ (v1_partfun1 @ X22 @ X21)
% 0.42/0.61          | ((k1_relat_1 @ X22) = (X21))
% 0.42/0.61          | ~ (v4_relat_1 @ X22 @ X21)
% 0.42/0.61          | ~ (v1_relat_1 @ X22))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.42/0.61  thf('163', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.42/0.61        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.42/0.61        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['161', '162'])).
% 0.42/0.61  thf('164', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['150', '151'])).
% 0.42/0.61  thf('165', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['142', '143'])).
% 0.42/0.61  thf('166', plain,
% 0.42/0.61      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['163', '164', '165'])).
% 0.42/0.61  thf('167', plain,
% 0.42/0.61      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.61         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['140', '166'])).
% 0.42/0.61  thf('168', plain,
% 0.42/0.61      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.42/0.61         = (k2_funct_1 @ sk_C))),
% 0.42/0.61      inference('simplify', [status(thm)], ['123'])).
% 0.42/0.61  thf('169', plain,
% 0.42/0.61      (![X26 : $i]:
% 0.42/0.61         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.61  thf('170', plain,
% 0.42/0.61      (![X26 : $i]:
% 0.42/0.61         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.61  thf('171', plain,
% 0.42/0.61      (![X26 : $i]:
% 0.42/0.61         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.61  thf('172', plain,
% 0.42/0.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          != (k2_struct_0 @ sk_B)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('split', [status(esa)], ['32'])).
% 0.42/0.61  thf('173', plain,
% 0.42/0.61      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61           != (k2_struct_0 @ sk_B))
% 0.42/0.61         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['171', '172'])).
% 0.42/0.61  thf('174', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('175', plain,
% 0.42/0.61      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          != (k2_struct_0 @ sk_B)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)], ['173', '174'])).
% 0.42/0.61  thf('176', plain,
% 0.42/0.61      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61           != (k2_struct_0 @ sk_B))
% 0.42/0.61         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['170', '175'])).
% 0.42/0.61  thf('177', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('178', plain,
% 0.42/0.61      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          != (k2_struct_0 @ sk_B)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)], ['176', '177'])).
% 0.42/0.61  thf('179', plain,
% 0.42/0.61      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61           != (k2_struct_0 @ sk_B))
% 0.42/0.61         | ~ (l1_struct_0 @ sk_A)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['169', '178'])).
% 0.42/0.61  thf('180', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('181', plain,
% 0.42/0.61      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          != (k2_struct_0 @ sk_B)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)], ['179', '180'])).
% 0.42/0.61  thf('182', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('183', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['72', '75', '78'])).
% 0.42/0.61  thf('184', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['99', '100', '103'])).
% 0.42/0.61  thf('185', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('186', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('187', plain,
% 0.42/0.61      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.61          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.42/0.61          != (k2_relat_1 @ sk_C)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)],
% 0.42/0.61                ['181', '182', '183', '184', '185', '186'])).
% 0.42/0.61  thf('188', plain,
% 0.42/0.61      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.61          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['168', '187'])).
% 0.42/0.61  thf('189', plain,
% 0.42/0.61      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61                = (k2_struct_0 @ sk_B))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['167', '188'])).
% 0.42/0.61  thf('190', plain,
% 0.42/0.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          = (k2_struct_0 @ sk_B)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['189'])).
% 0.42/0.61  thf('191', plain,
% 0.42/0.61      (~
% 0.42/0.61       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          = (k2_struct_0 @ sk_A))) | 
% 0.42/0.61       ~
% 0.42/0.61       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          = (k2_struct_0 @ sk_B)))),
% 0.42/0.61      inference('split', [status(esa)], ['32'])).
% 0.42/0.61  thf('192', plain,
% 0.42/0.61      (~
% 0.42/0.61       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.61          = (k2_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sat_resolution*', [status(thm)], ['190', '191'])).
% 0.42/0.61  thf('193', plain,
% 0.42/0.61      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.42/0.61      inference('simpl_trail', [status(thm)], ['137', '192'])).
% 0.42/0.61  thf('194', plain,
% 0.42/0.61      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.42/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['29', '193'])).
% 0.42/0.61  thf('195', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.42/0.61  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('197', plain, ((v2_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('198', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 0.42/0.61  thf('199', plain, ($false), inference('simplify', [status(thm)], ['198'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
