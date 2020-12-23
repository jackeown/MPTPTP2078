%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Guk4V0OMQ7

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:25 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 323 expanded)
%              Number of leaves         :   29 ( 108 expanded)
%              Depth                    :   17
%              Number of atoms          : 1672 (8414 expanded)
%              Number of equality atoms :   87 ( 249 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
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
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X13 @ X15 )
       != X13 )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k2_tops_2 @ X14 @ X13 @ X15 )
        = ( k2_funct_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
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
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
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
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
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

thf('28',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relset_1 @ X11 @ X10 @ X9 )
       != X10 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X9 @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36'])).

thf('38',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X13 @ X15 )
       != X13 )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k2_tops_2 @ X14 @ X13 @ X15 )
        = ( k2_funct_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relset_1 @ X11 @ X10 @ X9 )
       != X10 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X9 @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('49',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('50',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relset_1 @ X11 @ X10 @ X9 )
       != X10 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X9 ) @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X9 @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','52','65'])).

thf('67',plain,(
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

thf('68',plain,(
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

thf('69',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X13 @ X15 )
       != X13 )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k2_tops_2 @ X14 @ X13 @ X15 )
        = ( k2_funct_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','85','86','87','88'])).

thf('90',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
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

thf('92',plain,(
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

thf('93',plain,
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
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['84'])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['93','94','95','96','97','98','99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','90','104'])).

thf('106',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['28','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['27','109'])).

thf('111',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','110'])).

thf('112',plain,(
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

thf('113',plain,(
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

thf('114',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_funct_2 @ X6 @ X7 @ X8 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['112','114'])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('121',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('122',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['111','118','123','124','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Guk4V0OMQ7
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.33/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.33/0.54  % Solved by: fo/fo7.sh
% 0.33/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.54  % done 260 iterations in 0.086s
% 0.33/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.33/0.54  % SZS output start Refutation
% 0.33/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.33/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.33/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.33/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.33/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.33/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.33/0.54  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.33/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.33/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.33/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.33/0.54  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.33/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.33/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.33/0.54  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.33/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.33/0.54  thf(t65_funct_1, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.33/0.54       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.33/0.54  thf('0', plain,
% 0.33/0.54      (![X4 : $i]:
% 0.33/0.54         (~ (v2_funct_1 @ X4)
% 0.33/0.54          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.33/0.54          | ~ (v1_funct_1 @ X4)
% 0.33/0.54          | ~ (v1_relat_1 @ X4))),
% 0.33/0.54      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.33/0.54  thf(d3_struct_0, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.33/0.54  thf('1', plain,
% 0.33/0.54      (![X12 : $i]:
% 0.33/0.54         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.33/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.33/0.54  thf(t64_tops_2, conjecture,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( l1_struct_0 @ A ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.33/0.54           ( ![C:$i]:
% 0.33/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.33/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.33/0.54                 ( m1_subset_1 @
% 0.33/0.54                   C @ 
% 0.33/0.54                   ( k1_zfmisc_1 @
% 0.33/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.33/0.54               ( ( ( ( k2_relset_1 @
% 0.33/0.54                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.33/0.54                     ( k2_struct_0 @ B ) ) & 
% 0.33/0.54                   ( v2_funct_1 @ C ) ) =>
% 0.33/0.54                 ( r2_funct_2 @
% 0.33/0.54                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.33/0.54                   ( k2_tops_2 @
% 0.33/0.54                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.33/0.54                     ( k2_tops_2 @
% 0.33/0.54                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.33/0.54                   C ) ) ) ) ) ) ))).
% 0.33/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.54    (~( ![A:$i]:
% 0.33/0.54        ( ( l1_struct_0 @ A ) =>
% 0.33/0.54          ( ![B:$i]:
% 0.33/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.33/0.54              ( ![C:$i]:
% 0.33/0.54                ( ( ( v1_funct_1 @ C ) & 
% 0.33/0.54                    ( v1_funct_2 @
% 0.33/0.54                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.33/0.54                    ( m1_subset_1 @
% 0.33/0.54                      C @ 
% 0.33/0.54                      ( k1_zfmisc_1 @
% 0.33/0.54                        ( k2_zfmisc_1 @
% 0.33/0.54                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.33/0.54                  ( ( ( ( k2_relset_1 @
% 0.33/0.54                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.33/0.54                        ( k2_struct_0 @ B ) ) & 
% 0.33/0.54                      ( v2_funct_1 @ C ) ) =>
% 0.33/0.54                    ( r2_funct_2 @
% 0.33/0.54                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.33/0.54                      ( k2_tops_2 @
% 0.33/0.54                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.33/0.54                        ( k2_tops_2 @
% 0.33/0.54                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.33/0.54                      C ) ) ) ) ) ) ) )),
% 0.33/0.54    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.33/0.54  thf('2', plain,
% 0.33/0.54      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.33/0.54          sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('3', plain,
% 0.33/0.54      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.33/0.54           sk_C)
% 0.33/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.33/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.33/0.54  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('5', plain,
% 0.33/0.54      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.33/0.54          sk_C)),
% 0.33/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.33/0.54  thf('6', plain,
% 0.33/0.54      (![X12 : $i]:
% 0.33/0.54         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.33/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.33/0.54  thf('7', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('8', plain,
% 0.33/0.54      (((m1_subset_1 @ sk_C @ 
% 0.33/0.54         (k1_zfmisc_1 @ 
% 0.33/0.54          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.33/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.33/0.54      inference('sup+', [status(thm)], ['6', '7'])).
% 0.33/0.54  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('10', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.33/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.33/0.54  thf(d4_tops_2, axiom,
% 0.33/0.54    (![A:$i,B:$i,C:$i]:
% 0.33/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.33/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.33/0.54       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.33/0.54         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.33/0.54  thf('11', plain,
% 0.33/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.33/0.54         (((k2_relset_1 @ X14 @ X13 @ X15) != (X13))
% 0.33/0.54          | ~ (v2_funct_1 @ X15)
% 0.33/0.54          | ((k2_tops_2 @ X14 @ X13 @ X15) = (k2_funct_1 @ X15))
% 0.33/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13)))
% 0.33/0.54          | ~ (v1_funct_2 @ X15 @ X14 @ X13)
% 0.33/0.54          | ~ (v1_funct_1 @ X15))),
% 0.33/0.54      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.33/0.54  thf('12', plain,
% 0.33/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.33/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.33/0.54        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54            = (k2_funct_1 @ sk_C))
% 0.33/0.54        | ~ (v2_funct_1 @ sk_C)
% 0.33/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54            != (k2_struct_0 @ sk_B)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.33/0.54  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('14', plain,
% 0.33/0.54      (![X12 : $i]:
% 0.33/0.54         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.33/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.33/0.54  thf('15', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('16', plain,
% 0.33/0.54      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.33/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.33/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.33/0.54  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('18', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.33/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.33/0.54  thf('19', plain, ((v2_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('20', plain,
% 0.33/0.54      (![X12 : $i]:
% 0.33/0.54         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.33/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.33/0.54  thf('21', plain,
% 0.33/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54         = (k2_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('22', plain,
% 0.33/0.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54          = (k2_struct_0 @ sk_B))
% 0.33/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.33/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.33/0.54  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('24', plain,
% 0.33/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54         = (k2_struct_0 @ sk_B))),
% 0.33/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.33/0.54  thf('25', plain,
% 0.33/0.54      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54          = (k2_funct_1 @ sk_C))
% 0.33/0.54        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.33/0.54      inference('demod', [status(thm)], ['12', '13', '18', '19', '24'])).
% 0.33/0.54  thf('26', plain,
% 0.33/0.54      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54         = (k2_funct_1 @ sk_C))),
% 0.33/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.33/0.54  thf('27', plain,
% 0.33/0.54      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54           (k2_funct_1 @ sk_C)) @ 
% 0.33/0.54          sk_C)),
% 0.33/0.54      inference('demod', [status(thm)], ['5', '26'])).
% 0.33/0.54  thf('28', plain,
% 0.33/0.54      (![X12 : $i]:
% 0.33/0.54         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.33/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.33/0.54  thf('29', plain,
% 0.33/0.54      (![X12 : $i]:
% 0.33/0.54         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.33/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.33/0.54  thf('30', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(t31_funct_2, axiom,
% 0.33/0.54    (![A:$i,B:$i,C:$i]:
% 0.33/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.33/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.33/0.54       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.33/0.54         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.33/0.54           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.33/0.54           ( m1_subset_1 @
% 0.33/0.54             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.33/0.54  thf('31', plain,
% 0.33/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.33/0.54         (~ (v2_funct_1 @ X9)
% 0.33/0.54          | ((k2_relset_1 @ X11 @ X10 @ X9) != (X10))
% 0.33/0.54          | (m1_subset_1 @ (k2_funct_1 @ X9) @ 
% 0.33/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.33/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.33/0.54          | ~ (v1_funct_2 @ X9 @ X11 @ X10)
% 0.33/0.54          | ~ (v1_funct_1 @ X9))),
% 0.33/0.54      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.33/0.54  thf('32', plain,
% 0.33/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.33/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.33/0.54        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.33/0.54           (k1_zfmisc_1 @ 
% 0.33/0.54            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.33/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54            != (u1_struct_0 @ sk_B))
% 0.33/0.54        | ~ (v2_funct_1 @ sk_C))),
% 0.33/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.33/0.54  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('34', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('35', plain,
% 0.33/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54         = (k2_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('36', plain, ((v2_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('37', plain,
% 0.33/0.54      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.33/0.54         (k1_zfmisc_1 @ 
% 0.33/0.54          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.33/0.54        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.33/0.54      inference('demod', [status(thm)], ['32', '33', '34', '35', '36'])).
% 0.33/0.54  thf('38', plain,
% 0.33/0.54      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.33/0.54        | ~ (l1_struct_0 @ sk_B)
% 0.33/0.54        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.33/0.54           (k1_zfmisc_1 @ 
% 0.33/0.54            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.33/0.54      inference('sup-', [status(thm)], ['29', '37'])).
% 0.33/0.54  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('40', plain,
% 0.33/0.54      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.33/0.54        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.33/0.54           (k1_zfmisc_1 @ 
% 0.33/0.54            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.33/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.33/0.54  thf('41', plain,
% 0.33/0.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.33/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.33/0.54  thf('42', plain,
% 0.33/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.33/0.54         (((k2_relset_1 @ X14 @ X13 @ X15) != (X13))
% 0.33/0.54          | ~ (v2_funct_1 @ X15)
% 0.33/0.54          | ((k2_tops_2 @ X14 @ X13 @ X15) = (k2_funct_1 @ X15))
% 0.33/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13)))
% 0.33/0.54          | ~ (v1_funct_2 @ X15 @ X14 @ X13)
% 0.33/0.54          | ~ (v1_funct_1 @ X15))),
% 0.33/0.54      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.33/0.54  thf('43', plain,
% 0.33/0.54      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.33/0.54        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54             (u1_struct_0 @ sk_A))
% 0.33/0.54        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.33/0.54        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.33/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.33/0.54  thf('44', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.33/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.33/0.54  thf('45', plain,
% 0.33/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.33/0.54         (~ (v2_funct_1 @ X9)
% 0.33/0.54          | ((k2_relset_1 @ X11 @ X10 @ X9) != (X10))
% 0.33/0.54          | (v1_funct_1 @ (k2_funct_1 @ X9))
% 0.33/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.33/0.54          | ~ (v1_funct_2 @ X9 @ X11 @ X10)
% 0.33/0.54          | ~ (v1_funct_1 @ X9))),
% 0.33/0.54      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.33/0.54  thf('46', plain,
% 0.33/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.33/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.33/0.54        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.33/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54            != (k2_struct_0 @ sk_B))
% 0.33/0.54        | ~ (v2_funct_1 @ sk_C))),
% 0.33/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.33/0.54  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('48', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.33/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.33/0.54  thf('49', plain,
% 0.33/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54         = (k2_struct_0 @ sk_B))),
% 0.33/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.33/0.54  thf('50', plain, ((v2_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('51', plain,
% 0.33/0.54      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.33/0.54        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.33/0.54      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 0.33/0.54  thf('52', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.33/0.54      inference('simplify', [status(thm)], ['51'])).
% 0.33/0.54  thf('53', plain,
% 0.33/0.54      (![X12 : $i]:
% 0.33/0.54         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.33/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.33/0.54  thf('54', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('55', plain,
% 0.33/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.33/0.54         (~ (v2_funct_1 @ X9)
% 0.33/0.54          | ((k2_relset_1 @ X11 @ X10 @ X9) != (X10))
% 0.33/0.54          | (v1_funct_2 @ (k2_funct_1 @ X9) @ X10 @ X11)
% 0.33/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.33/0.54          | ~ (v1_funct_2 @ X9 @ X11 @ X10)
% 0.33/0.54          | ~ (v1_funct_1 @ X9))),
% 0.33/0.54      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.33/0.54  thf('56', plain,
% 0.33/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.33/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.33/0.54        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54           (u1_struct_0 @ sk_A))
% 0.33/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54            != (u1_struct_0 @ sk_B))
% 0.33/0.54        | ~ (v2_funct_1 @ sk_C))),
% 0.33/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.33/0.54  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('58', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('59', plain,
% 0.33/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54         = (k2_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('60', plain, ((v2_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('61', plain,
% 0.33/0.54      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54         (u1_struct_0 @ sk_A))
% 0.33/0.54        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.33/0.54      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.33/0.54  thf('62', plain,
% 0.33/0.54      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.33/0.54        | ~ (l1_struct_0 @ sk_B)
% 0.33/0.54        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54           (u1_struct_0 @ sk_A)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['53', '61'])).
% 0.33/0.54  thf('63', plain, ((l1_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('64', plain,
% 0.33/0.54      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.33/0.54        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54           (u1_struct_0 @ sk_A)))),
% 0.33/0.54      inference('demod', [status(thm)], ['62', '63'])).
% 0.33/0.54  thf('65', plain,
% 0.33/0.54      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54        (u1_struct_0 @ sk_A))),
% 0.33/0.54      inference('simplify', [status(thm)], ['64'])).
% 0.33/0.54  thf('66', plain,
% 0.33/0.54      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.33/0.54        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.33/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.33/0.54      inference('demod', [status(thm)], ['43', '52', '65'])).
% 0.33/0.54  thf('67', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(t63_tops_2, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( l1_struct_0 @ A ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( l1_struct_0 @ B ) =>
% 0.33/0.54           ( ![C:$i]:
% 0.33/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.33/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.33/0.54                 ( m1_subset_1 @
% 0.33/0.54                   C @ 
% 0.33/0.54                   ( k1_zfmisc_1 @
% 0.33/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.33/0.54               ( ( ( ( k2_relset_1 @
% 0.33/0.54                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.33/0.54                     ( k2_struct_0 @ B ) ) & 
% 0.33/0.54                   ( v2_funct_1 @ C ) ) =>
% 0.33/0.54                 ( v2_funct_1 @
% 0.33/0.54                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.33/0.54  thf('68', plain,
% 0.33/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.33/0.54         (~ (l1_struct_0 @ X19)
% 0.33/0.54          | ((k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21)
% 0.33/0.54              != (k2_struct_0 @ X19))
% 0.33/0.54          | ~ (v2_funct_1 @ X21)
% 0.33/0.54          | (v2_funct_1 @ 
% 0.33/0.54             (k2_tops_2 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21))
% 0.33/0.54          | ~ (m1_subset_1 @ X21 @ 
% 0.33/0.54               (k1_zfmisc_1 @ 
% 0.33/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.33/0.54          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.33/0.54          | ~ (v1_funct_1 @ X21)
% 0.33/0.54          | ~ (l1_struct_0 @ X20))),
% 0.33/0.54      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.33/0.54  thf('69', plain,
% 0.33/0.54      ((~ (l1_struct_0 @ sk_A)
% 0.33/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.33/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.33/0.54        | (v2_funct_1 @ 
% 0.33/0.54           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.33/0.54        | ~ (v2_funct_1 @ sk_C)
% 0.33/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54            != (k2_struct_0 @ sk_B))
% 0.33/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.33/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.33/0.54  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('72', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('73', plain,
% 0.33/0.54      (![X12 : $i]:
% 0.33/0.54         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.33/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.33/0.54  thf('74', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('75', plain,
% 0.33/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.33/0.54         (((k2_relset_1 @ X14 @ X13 @ X15) != (X13))
% 0.33/0.54          | ~ (v2_funct_1 @ X15)
% 0.33/0.54          | ((k2_tops_2 @ X14 @ X13 @ X15) = (k2_funct_1 @ X15))
% 0.33/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13)))
% 0.33/0.54          | ~ (v1_funct_2 @ X15 @ X14 @ X13)
% 0.33/0.54          | ~ (v1_funct_1 @ X15))),
% 0.33/0.54      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.33/0.54  thf('76', plain,
% 0.33/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.33/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.33/0.54        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54            = (k2_funct_1 @ sk_C))
% 0.33/0.54        | ~ (v2_funct_1 @ sk_C)
% 0.33/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54            != (u1_struct_0 @ sk_B)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['74', '75'])).
% 0.33/0.54  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('78', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('79', plain, ((v2_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('80', plain,
% 0.33/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54         = (k2_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('81', plain,
% 0.33/0.54      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54          = (k2_funct_1 @ sk_C))
% 0.33/0.54        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.33/0.54      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.33/0.54  thf('82', plain,
% 0.33/0.54      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.33/0.54        | ~ (l1_struct_0 @ sk_B)
% 0.33/0.54        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54            = (k2_funct_1 @ sk_C)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['73', '81'])).
% 0.33/0.54  thf('83', plain, ((l1_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('84', plain,
% 0.33/0.54      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.33/0.54        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54            = (k2_funct_1 @ sk_C)))),
% 0.33/0.54      inference('demod', [status(thm)], ['82', '83'])).
% 0.33/0.54  thf('85', plain,
% 0.33/0.54      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54         = (k2_funct_1 @ sk_C))),
% 0.33/0.54      inference('simplify', [status(thm)], ['84'])).
% 0.33/0.54  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('87', plain,
% 0.33/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54         = (k2_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('89', plain,
% 0.33/0.54      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.33/0.54        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.33/0.54      inference('demod', [status(thm)],
% 0.33/0.54                ['69', '70', '71', '72', '85', '86', '87', '88'])).
% 0.33/0.54  thf('90', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.33/0.54      inference('simplify', [status(thm)], ['89'])).
% 0.33/0.54  thf('91', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(t62_tops_2, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( l1_struct_0 @ A ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.33/0.54           ( ![C:$i]:
% 0.33/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.33/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.33/0.54                 ( m1_subset_1 @
% 0.33/0.54                   C @ 
% 0.33/0.54                   ( k1_zfmisc_1 @
% 0.33/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.33/0.54               ( ( ( ( k2_relset_1 @
% 0.33/0.54                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.33/0.54                     ( k2_struct_0 @ B ) ) & 
% 0.33/0.54                   ( v2_funct_1 @ C ) ) =>
% 0.33/0.54                 ( ( ( k1_relset_1 @
% 0.33/0.54                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.33/0.54                       ( k2_tops_2 @
% 0.33/0.54                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.33/0.54                     ( k2_struct_0 @ B ) ) & 
% 0.33/0.54                   ( ( k2_relset_1 @
% 0.33/0.54                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.33/0.54                       ( k2_tops_2 @
% 0.33/0.54                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.33/0.54                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.33/0.54  thf('92', plain,
% 0.33/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.33/0.54         ((v2_struct_0 @ X16)
% 0.33/0.54          | ~ (l1_struct_0 @ X16)
% 0.33/0.54          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.33/0.54              != (k2_struct_0 @ X16))
% 0.33/0.54          | ~ (v2_funct_1 @ X18)
% 0.33/0.54          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.33/0.54              (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.33/0.54              = (k2_struct_0 @ X17))
% 0.33/0.54          | ~ (m1_subset_1 @ X18 @ 
% 0.33/0.54               (k1_zfmisc_1 @ 
% 0.33/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.33/0.54          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.33/0.54          | ~ (v1_funct_1 @ X18)
% 0.33/0.54          | ~ (l1_struct_0 @ X17))),
% 0.33/0.54      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.33/0.54  thf('93', plain,
% 0.33/0.54      ((~ (l1_struct_0 @ sk_A)
% 0.33/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.33/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.33/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.33/0.54            = (k2_struct_0 @ sk_A))
% 0.33/0.54        | ~ (v2_funct_1 @ sk_C)
% 0.33/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54            != (k2_struct_0 @ sk_B))
% 0.33/0.54        | ~ (l1_struct_0 @ sk_B)
% 0.33/0.54        | (v2_struct_0 @ sk_B))),
% 0.33/0.54      inference('sup-', [status(thm)], ['91', '92'])).
% 0.33/0.54  thf('94', plain, ((l1_struct_0 @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('96', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('97', plain,
% 0.33/0.54      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54         = (k2_funct_1 @ sk_C))),
% 0.33/0.54      inference('simplify', [status(thm)], ['84'])).
% 0.33/0.54  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('99', plain,
% 0.33/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.33/0.54         = (k2_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('100', plain, ((l1_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('101', plain,
% 0.33/0.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.33/0.54        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.33/0.54        | (v2_struct_0 @ sk_B))),
% 0.33/0.54      inference('demod', [status(thm)],
% 0.33/0.54                ['93', '94', '95', '96', '97', '98', '99', '100'])).
% 0.33/0.54  thf('102', plain,
% 0.33/0.54      (((v2_struct_0 @ sk_B)
% 0.33/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.33/0.54      inference('simplify', [status(thm)], ['101'])).
% 0.33/0.54  thf('103', plain, (~ (v2_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('104', plain,
% 0.33/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.33/0.54      inference('clc', [status(thm)], ['102', '103'])).
% 0.33/0.54  thf('105', plain,
% 0.33/0.54      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.33/0.54        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.33/0.54      inference('demod', [status(thm)], ['66', '90', '104'])).
% 0.33/0.54  thf('106', plain,
% 0.33/0.54      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.33/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.33/0.54        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.33/0.54      inference('sup-', [status(thm)], ['28', '105'])).
% 0.33/0.54  thf('107', plain, ((l1_struct_0 @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('108', plain,
% 0.33/0.54      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.33/0.54        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.33/0.54      inference('demod', [status(thm)], ['106', '107'])).
% 0.33/0.54  thf('109', plain,
% 0.33/0.54      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.54         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.33/0.54      inference('simplify', [status(thm)], ['108'])).
% 0.33/0.54  thf('110', plain,
% 0.33/0.54      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.33/0.54      inference('demod', [status(thm)], ['27', '109'])).
% 0.33/0.54  thf('111', plain,
% 0.33/0.54      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.33/0.54           sk_C)
% 0.33/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.33/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.33/0.54        | ~ (v2_funct_1 @ sk_C))),
% 0.33/0.54      inference('sup-', [status(thm)], ['0', '110'])).
% 0.33/0.54  thf('112', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(redefinition_r2_funct_2, axiom,
% 0.33/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.33/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.33/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.33/0.54         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.33/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.33/0.54       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.33/0.54  thf('113', plain,
% 0.33/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.33/0.54         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.33/0.54          | ~ (v1_funct_2 @ X5 @ X6 @ X7)
% 0.33/0.54          | ~ (v1_funct_1 @ X5)
% 0.33/0.54          | ~ (v1_funct_1 @ X8)
% 0.33/0.54          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.33/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.33/0.54          | (r2_funct_2 @ X6 @ X7 @ X5 @ X8)
% 0.33/0.54          | ((X5) != (X8)))),
% 0.33/0.54      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.33/0.54  thf('114', plain,
% 0.33/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.33/0.54         ((r2_funct_2 @ X6 @ X7 @ X8 @ X8)
% 0.33/0.54          | ~ (v1_funct_1 @ X8)
% 0.33/0.54          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.33/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.33/0.54      inference('simplify', [status(thm)], ['113'])).
% 0.33/0.54  thf('115', plain,
% 0.33/0.54      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.33/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.33/0.54        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.33/0.54           sk_C))),
% 0.33/0.54      inference('sup-', [status(thm)], ['112', '114'])).
% 0.33/0.54  thf('116', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('118', plain,
% 0.33/0.54      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.33/0.54      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.33/0.54  thf('119', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(cc2_relat_1, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( v1_relat_1 @ A ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.33/0.54  thf('120', plain,
% 0.33/0.54      (![X0 : $i, X1 : $i]:
% 0.33/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.33/0.54          | (v1_relat_1 @ X0)
% 0.33/0.54          | ~ (v1_relat_1 @ X1))),
% 0.33/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.33/0.54  thf('121', plain,
% 0.33/0.54      ((~ (v1_relat_1 @ 
% 0.33/0.54           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.33/0.54        | (v1_relat_1 @ sk_C))),
% 0.33/0.54      inference('sup-', [status(thm)], ['119', '120'])).
% 0.33/0.54  thf(fc6_relat_1, axiom,
% 0.33/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.33/0.54  thf('122', plain,
% 0.33/0.54      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.33/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.33/0.54  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 0.33/0.54      inference('demod', [status(thm)], ['121', '122'])).
% 0.33/0.54  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('126', plain, ($false),
% 0.33/0.54      inference('demod', [status(thm)], ['111', '118', '123', '124', '125'])).
% 0.33/0.54  
% 0.33/0.54  % SZS output end Refutation
% 0.33/0.54  
% 0.40/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
