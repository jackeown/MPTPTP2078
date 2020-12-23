%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hxh9u7KQwk

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:24 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 433 expanded)
%              Number of leaves         :   29 ( 140 expanded)
%              Depth                    :   15
%              Number of atoms          : 1861 (10941 expanded)
%              Number of equality atoms :   93 ( 330 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t64_tops_2,conjecture,(
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
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

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
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('2',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X10 @ X12 )
       != X10 )
      | ~ ( v2_funct_1 @ X12 )
      | ( ( k2_tops_2 @ X11 @ X10 @ X12 )
        = ( k2_funct_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','18','19','24'])).

thf('26',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','26'])).

thf('28',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('38',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X10 @ X12 )
       != X10 )
      | ~ ( v2_funct_1 @ X12 )
      | ( ( k2_tops_2 @ X11 @ X10 @ X12 )
        = ( k2_funct_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['63','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','61','62','71'])).

thf('73',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','73'])).

thf('75',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X10 @ X12 )
       != X10 )
      | ~ ( v2_funct_1 @ X12 )
      | ( ( k2_tops_2 @ X11 @ X10 @ X12 )
        = ( k2_funct_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X10 @ X12 )
       != X10 )
      | ~ ( v2_funct_1 @ X12 )
      | ( ( k2_tops_2 @ X11 @ X10 @ X12 )
        = ( k2_funct_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80','81','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('97',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('101',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('103',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('108',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('109',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('113',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['109','114','115'])).

thf('117',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','95','106','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_tops_2,axiom,(
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

thf('119',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 )
       != ( k2_struct_0 @ X19 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('120',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','125','126','127'])).

thf('129',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_2,axiom,(
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

thf('132',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X16 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 )
       != ( k2_struct_0 @ X16 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 ) )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('133',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134','135','136','137','138','139','140'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['130','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','129','147'])).

thf('149',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('151',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ( r2_funct_2 @ X6 @ X7 @ X5 @ X8 )
      | ( X5 != X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('152',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_funct_2 @ X6 @ X7 @ X8 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['150','152'])).

thf('154',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    $false ),
    inference(demod,[status(thm)],['30','149','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hxh9u7KQwk
% 0.15/0.38  % Computer   : n007.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 13:23:36 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.39/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.63  % Solved by: fo/fo7.sh
% 0.39/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.63  % done 282 iterations in 0.128s
% 0.39/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.63  % SZS output start Refutation
% 0.39/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.39/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.63  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.39/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.63  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.39/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.63  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.39/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.39/0.63  thf(d3_struct_0, axiom,
% 0.39/0.63    (![A:$i]:
% 0.39/0.63     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.39/0.63  thf('0', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf('1', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf(t64_tops_2, conjecture,
% 0.39/0.63    (![A:$i]:
% 0.39/0.63     ( ( l1_struct_0 @ A ) =>
% 0.39/0.63       ( ![B:$i]:
% 0.39/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.39/0.63           ( ![C:$i]:
% 0.39/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.63                 ( m1_subset_1 @
% 0.39/0.63                   C @ 
% 0.39/0.63                   ( k1_zfmisc_1 @
% 0.39/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.63               ( ( ( ( k2_relset_1 @
% 0.39/0.63                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.63                     ( k2_struct_0 @ B ) ) & 
% 0.39/0.63                   ( v2_funct_1 @ C ) ) =>
% 0.39/0.63                 ( r2_funct_2 @
% 0.39/0.63                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.39/0.63                   ( k2_tops_2 @
% 0.39/0.63                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.63                     ( k2_tops_2 @
% 0.39/0.63                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.39/0.63                   C ) ) ) ) ) ) ))).
% 0.39/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.63    (~( ![A:$i]:
% 0.39/0.63        ( ( l1_struct_0 @ A ) =>
% 0.39/0.63          ( ![B:$i]:
% 0.39/0.63            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.39/0.63              ( ![C:$i]:
% 0.39/0.63                ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.63                    ( v1_funct_2 @
% 0.39/0.63                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.63                    ( m1_subset_1 @
% 0.39/0.63                      C @ 
% 0.39/0.63                      ( k1_zfmisc_1 @
% 0.39/0.63                        ( k2_zfmisc_1 @
% 0.39/0.63                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.63                  ( ( ( ( k2_relset_1 @
% 0.39/0.63                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.63                        ( k2_struct_0 @ B ) ) & 
% 0.39/0.63                      ( v2_funct_1 @ C ) ) =>
% 0.39/0.63                    ( r2_funct_2 @
% 0.39/0.63                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.39/0.63                      ( k2_tops_2 @
% 0.39/0.63                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.63                        ( k2_tops_2 @
% 0.39/0.63                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.39/0.63                      C ) ) ) ) ) ) ) )),
% 0.39/0.63    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.39/0.63  thf('2', plain,
% 0.39/0.63      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.63          sk_C)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('3', plain,
% 0.39/0.63      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.63            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.63           sk_C)
% 0.39/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.63  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('5', plain,
% 0.39/0.63      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.63          sk_C)),
% 0.39/0.63      inference('demod', [status(thm)], ['3', '4'])).
% 0.39/0.63  thf('6', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf('7', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_C @ 
% 0.39/0.63        (k1_zfmisc_1 @ 
% 0.39/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('8', plain,
% 0.39/0.63      (((m1_subset_1 @ sk_C @ 
% 0.39/0.63         (k1_zfmisc_1 @ 
% 0.39/0.63          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.39/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['6', '7'])).
% 0.39/0.63  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('10', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_C @ 
% 0.39/0.63        (k1_zfmisc_1 @ 
% 0.39/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.63      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.63  thf(d4_tops_2, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.63       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.39/0.63         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.39/0.63  thf('11', plain,
% 0.39/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.63         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.39/0.63          | ~ (v2_funct_1 @ X12)
% 0.39/0.63          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.39/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.39/0.63          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.39/0.63          | ~ (v1_funct_1 @ X12))),
% 0.39/0.63      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.39/0.63  thf('12', plain,
% 0.39/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63            = (k2_funct_1 @ sk_C))
% 0.39/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63            != (k2_struct_0 @ sk_B)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.63  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('14', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf('15', plain,
% 0.39/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('16', plain,
% 0.39/0.63      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.63  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('18', plain,
% 0.39/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.63      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.63  thf('19', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('20', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf('21', plain,
% 0.39/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63         = (k2_struct_0 @ sk_B))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('22', plain,
% 0.39/0.63      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63          = (k2_struct_0 @ sk_B))
% 0.39/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['20', '21'])).
% 0.39/0.63  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('24', plain,
% 0.39/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63         = (k2_struct_0 @ sk_B))),
% 0.39/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.39/0.63  thf('25', plain,
% 0.39/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63          = (k2_funct_1 @ sk_C))
% 0.39/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.39/0.63      inference('demod', [status(thm)], ['12', '13', '18', '19', '24'])).
% 0.39/0.63  thf('26', plain,
% 0.39/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63         = (k2_funct_1 @ sk_C))),
% 0.39/0.63      inference('simplify', [status(thm)], ['25'])).
% 0.39/0.63  thf('27', plain,
% 0.39/0.63      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.63           (k2_funct_1 @ sk_C)) @ 
% 0.39/0.63          sk_C)),
% 0.39/0.63      inference('demod', [status(thm)], ['5', '26'])).
% 0.39/0.63  thf('28', plain,
% 0.39/0.63      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.63            (k2_funct_1 @ sk_C)) @ 
% 0.39/0.63           sk_C)
% 0.39/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.63      inference('sup-', [status(thm)], ['0', '27'])).
% 0.39/0.63  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('30', plain,
% 0.39/0.63      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.63           (k2_funct_1 @ sk_C)) @ 
% 0.39/0.63          sk_C)),
% 0.39/0.63      inference('demod', [status(thm)], ['28', '29'])).
% 0.39/0.63  thf('31', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf('32', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf('33', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_C @ 
% 0.39/0.63        (k1_zfmisc_1 @ 
% 0.39/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('34', plain,
% 0.39/0.63      (((m1_subset_1 @ sk_C @ 
% 0.39/0.63         (k1_zfmisc_1 @ 
% 0.39/0.63          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.39/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.63      inference('sup+', [status(thm)], ['32', '33'])).
% 0.39/0.63  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('36', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_C @ 
% 0.39/0.63        (k1_zfmisc_1 @ 
% 0.39/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.39/0.63  thf(dt_k2_tops_2, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.63       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.39/0.63         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.39/0.63         ( m1_subset_1 @
% 0.39/0.63           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.39/0.63           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.39/0.63  thf('37', plain,
% 0.39/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.63         ((m1_subset_1 @ (k2_tops_2 @ X13 @ X14 @ X15) @ 
% 0.39/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13)))
% 0.39/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.39/0.63          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.39/0.63          | ~ (v1_funct_1 @ X15))),
% 0.39/0.63      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.39/0.63  thf('38', plain,
% 0.39/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.63        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.63        | (m1_subset_1 @ 
% 0.39/0.63           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.39/0.63           (k1_zfmisc_1 @ 
% 0.39/0.63            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.39/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.63  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('40', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf('41', plain,
% 0.39/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('42', plain,
% 0.39/0.63      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.63      inference('sup+', [status(thm)], ['40', '41'])).
% 0.39/0.63  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('44', plain,
% 0.39/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.63      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.63  thf('45', plain,
% 0.39/0.63      ((m1_subset_1 @ 
% 0.39/0.63        (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.39/0.63        (k1_zfmisc_1 @ 
% 0.39/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.39/0.63      inference('demod', [status(thm)], ['38', '39', '44'])).
% 0.39/0.63  thf('46', plain,
% 0.39/0.63      (((m1_subset_1 @ 
% 0.39/0.63         (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.39/0.63         (k1_zfmisc_1 @ 
% 0.39/0.63          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.39/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['31', '45'])).
% 0.39/0.63  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('48', plain,
% 0.39/0.63      ((m1_subset_1 @ 
% 0.39/0.63        (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.39/0.63        (k1_zfmisc_1 @ 
% 0.39/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.39/0.63      inference('demod', [status(thm)], ['46', '47'])).
% 0.39/0.63  thf('49', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf('50', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_C @ 
% 0.39/0.63        (k1_zfmisc_1 @ 
% 0.39/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.39/0.63  thf('51', plain,
% 0.39/0.63      (((m1_subset_1 @ sk_C @ 
% 0.39/0.63         (k1_zfmisc_1 @ 
% 0.39/0.63          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.39/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.63  thf('52', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('53', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_C @ 
% 0.39/0.63        (k1_zfmisc_1 @ 
% 0.39/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.63      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.63  thf('54', plain,
% 0.39/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.63         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.39/0.63          | ~ (v2_funct_1 @ X12)
% 0.39/0.63          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.39/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.39/0.63          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.39/0.63          | ~ (v1_funct_1 @ X12))),
% 0.39/0.63      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.39/0.63  thf('55', plain,
% 0.39/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.63        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.63        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63            = (k2_funct_1 @ sk_C))
% 0.39/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.63        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63            != (k2_struct_0 @ sk_B)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.63  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('57', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf('58', plain,
% 0.39/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.63      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.63  thf('59', plain,
% 0.39/0.63      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['57', '58'])).
% 0.39/0.63  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('61', plain,
% 0.39/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.63      inference('demod', [status(thm)], ['59', '60'])).
% 0.39/0.63  thf('62', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('63', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf('64', plain,
% 0.39/0.63      (![X9 : $i]:
% 0.39/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.63  thf('65', plain,
% 0.39/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63         = (k2_struct_0 @ sk_B))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('66', plain,
% 0.39/0.63      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63          = (k2_struct_0 @ sk_B))
% 0.39/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.63      inference('sup+', [status(thm)], ['64', '65'])).
% 0.39/0.63  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('68', plain,
% 0.39/0.63      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63         = (k2_struct_0 @ sk_B))),
% 0.39/0.63      inference('demod', [status(thm)], ['66', '67'])).
% 0.39/0.63  thf('69', plain,
% 0.39/0.63      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63          = (k2_struct_0 @ sk_B))
% 0.39/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['63', '68'])).
% 0.39/0.63  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('71', plain,
% 0.39/0.63      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63         = (k2_struct_0 @ sk_B))),
% 0.39/0.63      inference('demod', [status(thm)], ['69', '70'])).
% 0.39/0.63  thf('72', plain,
% 0.39/0.63      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63          = (k2_funct_1 @ sk_C))
% 0.39/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.39/0.63      inference('demod', [status(thm)], ['55', '56', '61', '62', '71'])).
% 0.39/0.63  thf('73', plain,
% 0.39/0.63      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.63         = (k2_funct_1 @ sk_C))),
% 0.39/0.63      inference('simplify', [status(thm)], ['72'])).
% 0.39/0.63  thf('74', plain,
% 0.39/0.63      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.63        (k1_zfmisc_1 @ 
% 0.39/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.39/0.63      inference('demod', [status(thm)], ['48', '73'])).
% 0.45/0.63  thf('75', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.63         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.45/0.63          | ~ (v2_funct_1 @ X12)
% 0.45/0.63          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.45/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.45/0.63          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.45/0.63          | ~ (v1_funct_1 @ X12))),
% 0.45/0.63      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.63  thf('76', plain,
% 0.45/0.63      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.63        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.63             (k2_struct_0 @ sk_A))
% 0.45/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.63            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.63        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.63            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.63  thf('77', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ 
% 0.45/0.63        (k1_zfmisc_1 @ 
% 0.45/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('78', plain,
% 0.45/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.63         ((v1_funct_1 @ (k2_tops_2 @ X13 @ X14 @ X15))
% 0.45/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.45/0.63          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.45/0.63          | ~ (v1_funct_1 @ X15))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.45/0.63  thf('79', plain,
% 0.45/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (v1_funct_1 @ 
% 0.45/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.63  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('81', plain,
% 0.45/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('82', plain,
% 0.45/0.63      (![X9 : $i]:
% 0.45/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.63  thf('83', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ 
% 0.45/0.63        (k1_zfmisc_1 @ 
% 0.45/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('84', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.63         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.45/0.63          | ~ (v2_funct_1 @ X12)
% 0.45/0.63          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.45/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.45/0.63          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.45/0.63          | ~ (v1_funct_1 @ X12))),
% 0.45/0.63      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.63  thf('85', plain,
% 0.45/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63            = (k2_funct_1 @ sk_C))
% 0.45/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63            != (u1_struct_0 @ sk_B)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['83', '84'])).
% 0.45/0.63  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('87', plain,
% 0.45/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('89', plain,
% 0.45/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63         = (k2_struct_0 @ sk_B))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('90', plain,
% 0.45/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63          = (k2_funct_1 @ sk_C))
% 0.45/0.63        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.45/0.63      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 0.45/0.63  thf('91', plain,
% 0.45/0.63      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.45/0.63        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63            = (k2_funct_1 @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['82', '90'])).
% 0.45/0.63  thf('92', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('93', plain,
% 0.45/0.63      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.45/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63            = (k2_funct_1 @ sk_C)))),
% 0.45/0.63      inference('demod', [status(thm)], ['91', '92'])).
% 0.45/0.63  thf('94', plain,
% 0.45/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63         = (k2_funct_1 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['93'])).
% 0.45/0.63  thf('95', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['79', '80', '81', '94'])).
% 0.45/0.63  thf('96', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ 
% 0.45/0.63        (k1_zfmisc_1 @ 
% 0.45/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.63  thf('97', plain,
% 0.45/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.63         ((v1_funct_2 @ (k2_tops_2 @ X13 @ X14 @ X15) @ X14 @ X13)
% 0.45/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.45/0.63          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.45/0.63          | ~ (v1_funct_1 @ X15))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.45/0.63  thf('98', plain,
% 0.45/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.63        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (v1_funct_2 @ 
% 0.45/0.63           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.63           (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['96', '97'])).
% 0.45/0.63  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('100', plain,
% 0.45/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.63  thf('101', plain,
% 0.45/0.63      (![X9 : $i]:
% 0.45/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.63  thf('102', plain,
% 0.45/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63         = (k2_funct_1 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['93'])).
% 0.45/0.63  thf('103', plain,
% 0.45/0.63      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63          = (k2_funct_1 @ sk_C))
% 0.45/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.63      inference('sup+', [status(thm)], ['101', '102'])).
% 0.45/0.63  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('105', plain,
% 0.45/0.63      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63         = (k2_funct_1 @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['103', '104'])).
% 0.45/0.63  thf('106', plain,
% 0.45/0.63      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.63        (k2_struct_0 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['98', '99', '100', '105'])).
% 0.45/0.63  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t65_funct_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.63       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.45/0.63  thf('108', plain,
% 0.45/0.63      (![X4 : $i]:
% 0.45/0.63         (~ (v2_funct_1 @ X4)
% 0.45/0.63          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.45/0.63          | ~ (v1_funct_1 @ X4)
% 0.45/0.63          | ~ (v1_relat_1 @ X4))),
% 0.45/0.63      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.63  thf('109', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.63        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 0.45/0.63        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['107', '108'])).
% 0.45/0.63  thf('110', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ 
% 0.45/0.63        (k1_zfmisc_1 @ 
% 0.45/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc2_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.63  thf('111', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.63          | (v1_relat_1 @ X0)
% 0.45/0.63          | ~ (v1_relat_1 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.63  thf('112', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ 
% 0.45/0.63           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.45/0.63        | (v1_relat_1 @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['110', '111'])).
% 0.45/0.63  thf(fc6_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.63  thf('113', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.63  thf('114', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.63      inference('demod', [status(thm)], ['112', '113'])).
% 0.45/0.63  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('116', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['109', '114', '115'])).
% 0.45/0.63  thf('117', plain,
% 0.45/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.63          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.45/0.63        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.63            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['76', '95', '106', '116'])).
% 0.45/0.63  thf('118', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ 
% 0.45/0.63        (k1_zfmisc_1 @ 
% 0.45/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t63_tops_2, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_struct_0 @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( l1_struct_0 @ B ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.63                 ( m1_subset_1 @
% 0.45/0.63                   C @ 
% 0.45/0.63                   ( k1_zfmisc_1 @
% 0.45/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.63               ( ( ( ( k2_relset_1 @
% 0.45/0.63                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.63                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.63                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.63                 ( v2_funct_1 @
% 0.45/0.63                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('119', plain,
% 0.45/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.63         (~ (l1_struct_0 @ X19)
% 0.45/0.63          | ((k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21)
% 0.45/0.63              != (k2_struct_0 @ X19))
% 0.45/0.63          | ~ (v2_funct_1 @ X21)
% 0.45/0.63          | (v2_funct_1 @ 
% 0.45/0.63             (k2_tops_2 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21))
% 0.45/0.63          | ~ (m1_subset_1 @ X21 @ 
% 0.45/0.63               (k1_zfmisc_1 @ 
% 0.45/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.45/0.63          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.45/0.63          | ~ (v1_funct_1 @ X21)
% 0.45/0.63          | ~ (l1_struct_0 @ X20))),
% 0.45/0.63      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.45/0.63  thf('120', plain,
% 0.45/0.63      ((~ (l1_struct_0 @ sk_A)
% 0.45/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (v2_funct_1 @ 
% 0.45/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63            != (k2_struct_0 @ sk_B))
% 0.45/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['118', '119'])).
% 0.45/0.63  thf('121', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('123', plain,
% 0.45/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('124', plain,
% 0.45/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63         = (k2_funct_1 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['93'])).
% 0.45/0.63  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('126', plain,
% 0.45/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63         = (k2_struct_0 @ sk_B))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('127', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('128', plain,
% 0.45/0.63      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.63      inference('demod', [status(thm)],
% 0.45/0.63                ['120', '121', '122', '123', '124', '125', '126', '127'])).
% 0.45/0.63  thf('129', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['128'])).
% 0.45/0.63  thf('130', plain,
% 0.45/0.63      (![X9 : $i]:
% 0.45/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.63  thf('131', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ 
% 0.45/0.63        (k1_zfmisc_1 @ 
% 0.45/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t62_tops_2, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_struct_0 @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.63                 ( m1_subset_1 @
% 0.45/0.63                   C @ 
% 0.45/0.63                   ( k1_zfmisc_1 @
% 0.45/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.63               ( ( ( ( k2_relset_1 @
% 0.45/0.63                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.63                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.63                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.63                 ( ( ( k1_relset_1 @
% 0.45/0.63                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.63                       ( k2_tops_2 @
% 0.45/0.63                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.45/0.63                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.63                   ( ( k2_relset_1 @
% 0.45/0.63                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.63                       ( k2_tops_2 @
% 0.45/0.63                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.45/0.63                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('132', plain,
% 0.45/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.63         ((v2_struct_0 @ X16)
% 0.45/0.63          | ~ (l1_struct_0 @ X16)
% 0.45/0.63          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.45/0.63              != (k2_struct_0 @ X16))
% 0.45/0.63          | ~ (v2_funct_1 @ X18)
% 0.45/0.63          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.45/0.63              (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.45/0.63              = (k2_struct_0 @ X17))
% 0.45/0.63          | ~ (m1_subset_1 @ X18 @ 
% 0.45/0.63               (k1_zfmisc_1 @ 
% 0.45/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.45/0.63          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.45/0.63          | ~ (v1_funct_1 @ X18)
% 0.45/0.63          | ~ (l1_struct_0 @ X17))),
% 0.45/0.63      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.45/0.63  thf('133', plain,
% 0.45/0.63      ((~ (l1_struct_0 @ sk_A)
% 0.45/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.63            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.63            = (k2_struct_0 @ sk_A))
% 0.45/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63            != (k2_struct_0 @ sk_B))
% 0.45/0.63        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['131', '132'])).
% 0.45/0.63  thf('134', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('136', plain,
% 0.45/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('137', plain,
% 0.45/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63         = (k2_funct_1 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['93'])).
% 0.45/0.63  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('139', plain,
% 0.45/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.63         = (k2_struct_0 @ sk_B))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('140', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('141', plain,
% 0.45/0.63      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.63          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.45/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.45/0.63        | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)],
% 0.45/0.63                ['133', '134', '135', '136', '137', '138', '139', '140'])).
% 0.45/0.63  thf('142', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B)
% 0.45/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.63            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['141'])).
% 0.45/0.63  thf('143', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('144', plain,
% 0.45/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.63         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.45/0.63      inference('clc', [status(thm)], ['142', '143'])).
% 0.45/0.63  thf('145', plain,
% 0.45/0.63      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.63          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.45/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.63      inference('sup+', [status(thm)], ['130', '144'])).
% 0.45/0.63  thf('146', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('147', plain,
% 0.45/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.63         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['145', '146'])).
% 0.45/0.63  thf('148', plain,
% 0.45/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.63          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.45/0.63        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['117', '129', '147'])).
% 0.45/0.63  thf('149', plain,
% 0.45/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.63         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['148'])).
% 0.45/0.63  thf('150', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ 
% 0.45/0.63        (k1_zfmisc_1 @ 
% 0.45/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_r2_funct_2, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.63         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.63       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.45/0.63  thf('151', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.45/0.63          | ~ (v1_funct_2 @ X5 @ X6 @ X7)
% 0.45/0.63          | ~ (v1_funct_1 @ X5)
% 0.45/0.63          | ~ (v1_funct_1 @ X8)
% 0.45/0.63          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.45/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.45/0.63          | (r2_funct_2 @ X6 @ X7 @ X5 @ X8)
% 0.45/0.63          | ((X5) != (X8)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.45/0.63  thf('152', plain,
% 0.45/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.63         ((r2_funct_2 @ X6 @ X7 @ X8 @ X8)
% 0.45/0.63          | ~ (v1_funct_1 @ X8)
% 0.45/0.63          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.45/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['151'])).
% 0.45/0.63  thf('153', plain,
% 0.45/0.63      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.63        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.63           sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['150', '152'])).
% 0.45/0.63  thf('154', plain,
% 0.45/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('156', plain,
% 0.45/0.63      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.63      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.45/0.63  thf('157', plain, ($false),
% 0.45/0.63      inference('demod', [status(thm)], ['30', '149', '156'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
