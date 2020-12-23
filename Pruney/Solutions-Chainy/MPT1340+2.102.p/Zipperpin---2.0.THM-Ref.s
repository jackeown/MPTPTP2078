%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t5wLr64tPW

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:25 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 289 expanded)
%              Number of leaves         :   29 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          : 1586 (7199 expanded)
%              Number of equality atoms :   85 ( 212 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
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
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X14 @ X16 )
       != X14 )
      | ~ ( v2_funct_1 @ X16 )
      | ( ( k2_tops_2 @ X15 @ X14 @ X16 )
        = ( k2_funct_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
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
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
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
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
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
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('30',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relset_1 @ X12 @ X11 @ X10 )
       != X11 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X14 @ X16 )
       != X14 )
      | ~ ( v2_funct_1 @ X16 )
      | ( ( k2_tops_2 @ X15 @ X14 @ X16 )
        = ( k2_funct_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relset_1 @ X12 @ X11 @ X10 )
       != X11 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('50',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('51',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relset_1 @ X12 @ X11 @ X10 )
       != X11 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X10 ) @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','53','66'])).

thf('68',plain,(
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

thf('69',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X17 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ X19 )
       != ( k2_struct_0 @ X17 ) )
      | ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ X19 ) )
        = ( k2_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('70',plain,
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
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X14 @ X16 )
       != X14 )
      | ~ ( v2_funct_1 @ X16 )
      | ( ( k2_tops_2 @ X15 @ X14 @ X16 )
        = ( k2_funct_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','71','72','73','86','87','88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','93'])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['29','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('99',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['95','100','101','102'])).

thf('104',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['28','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['27','107'])).

thf('109',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','108'])).

thf('110',plain,(
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

thf('111',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( r2_funct_2 @ X7 @ X8 @ X6 @ X9 )
      | ( X6 != X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('112',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_funct_2 @ X7 @ X8 @ X9 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['98','99'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['109','116','117','118','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t5wLr64tPW
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:26:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 240 iterations in 0.113s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.58  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.37/0.58  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.58  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.37/0.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.58  thf(t65_funct_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.58       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      (![X5 : $i]:
% 0.37/0.58         (~ (v2_funct_1 @ X5)
% 0.37/0.58          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.37/0.58          | ~ (v1_funct_1 @ X5)
% 0.37/0.58          | ~ (v1_relat_1 @ X5))),
% 0.37/0.58      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.37/0.58  thf(d3_struct_0, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X13 : $i]:
% 0.37/0.58         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.58  thf(t64_tops_2, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_struct_0 @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.37/0.58           ( ![C:$i]:
% 0.37/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.58                 ( m1_subset_1 @
% 0.37/0.58                   C @ 
% 0.37/0.58                   ( k1_zfmisc_1 @
% 0.37/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.58               ( ( ( ( k2_relset_1 @
% 0.37/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.58                     ( k2_struct_0 @ B ) ) & 
% 0.37/0.58                   ( v2_funct_1 @ C ) ) =>
% 0.37/0.58                 ( r2_funct_2 @
% 0.37/0.58                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.37/0.58                   ( k2_tops_2 @
% 0.37/0.58                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.58                     ( k2_tops_2 @
% 0.37/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.37/0.58                   C ) ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( l1_struct_0 @ A ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.37/0.58              ( ![C:$i]:
% 0.37/0.58                ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.58                    ( v1_funct_2 @
% 0.37/0.58                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.58                    ( m1_subset_1 @
% 0.37/0.58                      C @ 
% 0.37/0.58                      ( k1_zfmisc_1 @
% 0.37/0.58                        ( k2_zfmisc_1 @
% 0.37/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.58                  ( ( ( ( k2_relset_1 @
% 0.37/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.58                        ( k2_struct_0 @ B ) ) & 
% 0.37/0.58                      ( v2_funct_1 @ C ) ) =>
% 0.37/0.58                    ( r2_funct_2 @
% 0.37/0.58                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.37/0.58                      ( k2_tops_2 @
% 0.37/0.58                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.58                        ( k2_tops_2 @
% 0.37/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.37/0.58                      C ) ) ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.37/0.58          sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.37/0.58           sk_C)
% 0.37/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.58  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.37/0.58          sk_C)),
% 0.37/0.58      inference('demod', [status(thm)], ['3', '4'])).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (![X13 : $i]:
% 0.37/0.58         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ 
% 0.37/0.58        (k1_zfmisc_1 @ 
% 0.37/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (((m1_subset_1 @ sk_C @ 
% 0.37/0.58         (k1_zfmisc_1 @ 
% 0.37/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.37/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.37/0.58  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ 
% 0.37/0.58        (k1_zfmisc_1 @ 
% 0.37/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.37/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf(d4_tops_2, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.58       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.37/0.58         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.58         (((k2_relset_1 @ X15 @ X14 @ X16) != (X14))
% 0.37/0.58          | ~ (v2_funct_1 @ X16)
% 0.37/0.58          | ((k2_tops_2 @ X15 @ X14 @ X16) = (k2_funct_1 @ X16))
% 0.37/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14)))
% 0.37/0.58          | ~ (v1_funct_2 @ X16 @ X15 @ X14)
% 0.37/0.58          | ~ (v1_funct_1 @ X16))),
% 0.37/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.37/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58            = (k2_funct_1 @ sk_C))
% 0.37/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58            != (k2_struct_0 @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X13 : $i]:
% 0.37/0.58         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.37/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.58  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.58  thf('19', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (![X13 : $i]:
% 0.37/0.58         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58         = (k2_struct_0 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58          = (k2_struct_0 @ sk_B))
% 0.37/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['20', '21'])).
% 0.37/0.58  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58         = (k2_struct_0 @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58          = (k2_funct_1 @ sk_C))
% 0.37/0.58        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.37/0.58      inference('demod', [status(thm)], ['12', '13', '18', '19', '24'])).
% 0.37/0.58  thf('26', plain,
% 0.37/0.58      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58         = (k2_funct_1 @ sk_C))),
% 0.37/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58           (k2_funct_1 @ sk_C)) @ 
% 0.37/0.58          sk_C)),
% 0.37/0.58      inference('demod', [status(thm)], ['5', '26'])).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      (![X13 : $i]:
% 0.37/0.58         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.58  thf(fc6_funct_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.37/0.58       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.37/0.58         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.37/0.58         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (![X4 : $i]:
% 0.37/0.58         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.37/0.58          | ~ (v2_funct_1 @ X4)
% 0.37/0.58          | ~ (v1_funct_1 @ X4)
% 0.37/0.58          | ~ (v1_relat_1 @ X4))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (![X13 : $i]:
% 0.37/0.58         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ 
% 0.37/0.58        (k1_zfmisc_1 @ 
% 0.37/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t31_funct_2, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.58       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.37/0.58         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.37/0.58           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.37/0.58           ( m1_subset_1 @
% 0.37/0.58             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.58         (~ (v2_funct_1 @ X10)
% 0.37/0.58          | ((k2_relset_1 @ X12 @ X11 @ X10) != (X11))
% 0.37/0.58          | (m1_subset_1 @ (k2_funct_1 @ X10) @ 
% 0.37/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.37/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.37/0.58          | ~ (v1_funct_2 @ X10 @ X12 @ X11)
% 0.37/0.58          | ~ (v1_funct_1 @ X10))),
% 0.37/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.58           (k1_zfmisc_1 @ 
% 0.37/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.37/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58            != (u1_struct_0 @ sk_B))
% 0.37/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.58  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58         = (k2_struct_0 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('37', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('38', plain,
% 0.37/0.58      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.58         (k1_zfmisc_1 @ 
% 0.37/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.37/0.58        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.37/0.58      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.37/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.37/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.58           (k1_zfmisc_1 @ 
% 0.37/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['30', '38'])).
% 0.37/0.58  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('41', plain,
% 0.37/0.58      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.37/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.58           (k1_zfmisc_1 @ 
% 0.37/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.58        (k1_zfmisc_1 @ 
% 0.37/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.37/0.58      inference('simplify', [status(thm)], ['41'])).
% 0.37/0.58  thf('43', plain,
% 0.37/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.58         (((k2_relset_1 @ X15 @ X14 @ X16) != (X14))
% 0.37/0.58          | ~ (v2_funct_1 @ X16)
% 0.37/0.58          | ((k2_tops_2 @ X15 @ X14 @ X16) = (k2_funct_1 @ X16))
% 0.37/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14)))
% 0.37/0.58          | ~ (v1_funct_2 @ X16 @ X15 @ X14)
% 0.37/0.58          | ~ (v1_funct_1 @ X16))),
% 0.37/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.37/0.58  thf('44', plain,
% 0.37/0.58      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.58        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58             (u1_struct_0 @ sk_A))
% 0.37/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.37/0.58        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ 
% 0.37/0.58        (k1_zfmisc_1 @ 
% 0.37/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.37/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.58         (~ (v2_funct_1 @ X10)
% 0.37/0.58          | ((k2_relset_1 @ X12 @ X11 @ X10) != (X11))
% 0.37/0.58          | (v1_funct_1 @ (k2_funct_1 @ X10))
% 0.37/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.37/0.58          | ~ (v1_funct_2 @ X10 @ X12 @ X11)
% 0.37/0.58          | ~ (v1_funct_1 @ X10))),
% 0.37/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.37/0.58        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58            != (k2_struct_0 @ sk_B))
% 0.37/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.58  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('49', plain,
% 0.37/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.58  thf('50', plain,
% 0.37/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58         = (k2_struct_0 @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.58  thf('51', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('52', plain,
% 0.37/0.58      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.58        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.37/0.58      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.37/0.58  thf('53', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.37/0.58      inference('simplify', [status(thm)], ['52'])).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      (![X13 : $i]:
% 0.37/0.58         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.58  thf('55', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ 
% 0.37/0.58        (k1_zfmisc_1 @ 
% 0.37/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('56', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.58         (~ (v2_funct_1 @ X10)
% 0.37/0.58          | ((k2_relset_1 @ X12 @ X11 @ X10) != (X11))
% 0.37/0.58          | (v1_funct_2 @ (k2_funct_1 @ X10) @ X11 @ X12)
% 0.37/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.37/0.58          | ~ (v1_funct_2 @ X10 @ X12 @ X11)
% 0.37/0.58          | ~ (v1_funct_1 @ X10))),
% 0.37/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.37/0.58  thf('57', plain,
% 0.37/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.58        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58           (u1_struct_0 @ sk_A))
% 0.37/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58            != (u1_struct_0 @ sk_B))
% 0.37/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.58  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('59', plain,
% 0.37/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('60', plain,
% 0.37/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58         = (k2_struct_0 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('61', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('62', plain,
% 0.37/0.58      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58         (u1_struct_0 @ sk_A))
% 0.37/0.58        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.37/0.58      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.37/0.58  thf('63', plain,
% 0.37/0.58      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.37/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.37/0.58        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58           (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['54', '62'])).
% 0.37/0.58  thf('64', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('65', plain,
% 0.37/0.58      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.37/0.58        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58           (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['63', '64'])).
% 0.37/0.58  thf('66', plain,
% 0.37/0.58      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58        (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('simplify', [status(thm)], ['65'])).
% 0.37/0.58  thf('67', plain,
% 0.37/0.58      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.37/0.58        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['44', '53', '66'])).
% 0.37/0.58  thf('68', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ 
% 0.37/0.58        (k1_zfmisc_1 @ 
% 0.37/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t62_tops_2, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_struct_0 @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.37/0.58           ( ![C:$i]:
% 0.37/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.58                 ( m1_subset_1 @
% 0.37/0.58                   C @ 
% 0.37/0.58                   ( k1_zfmisc_1 @
% 0.37/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.58               ( ( ( ( k2_relset_1 @
% 0.37/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.58                     ( k2_struct_0 @ B ) ) & 
% 0.37/0.58                   ( v2_funct_1 @ C ) ) =>
% 0.37/0.58                 ( ( ( k1_relset_1 @
% 0.37/0.58                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.58                       ( k2_tops_2 @
% 0.37/0.58                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.58                     ( k2_struct_0 @ B ) ) & 
% 0.37/0.58                   ( ( k2_relset_1 @
% 0.37/0.58                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.58                       ( k2_tops_2 @
% 0.37/0.58                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.58                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf('69', plain,
% 0.37/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.58         ((v2_struct_0 @ X17)
% 0.37/0.58          | ~ (l1_struct_0 @ X17)
% 0.37/0.58          | ((k2_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19)
% 0.37/0.58              != (k2_struct_0 @ X17))
% 0.37/0.58          | ~ (v2_funct_1 @ X19)
% 0.37/0.58          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18) @ 
% 0.37/0.58              (k2_tops_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19))
% 0.37/0.58              = (k2_struct_0 @ X18))
% 0.37/0.58          | ~ (m1_subset_1 @ X19 @ 
% 0.37/0.58               (k1_zfmisc_1 @ 
% 0.37/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))))
% 0.37/0.58          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))
% 0.37/0.58          | ~ (v1_funct_1 @ X19)
% 0.37/0.58          | ~ (l1_struct_0 @ X18))),
% 0.37/0.58      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.37/0.58  thf('70', plain,
% 0.37/0.58      ((~ (l1_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.58            = (k2_struct_0 @ sk_A))
% 0.37/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58            != (k2_struct_0 @ sk_B))
% 0.37/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.37/0.58        | (v2_struct_0 @ sk_B))),
% 0.37/0.58      inference('sup-', [status(thm)], ['68', '69'])).
% 0.37/0.58  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('73', plain,
% 0.37/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('74', plain,
% 0.37/0.58      (![X13 : $i]:
% 0.37/0.58         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.58  thf('75', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ 
% 0.37/0.58        (k1_zfmisc_1 @ 
% 0.37/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('76', plain,
% 0.37/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.58         (((k2_relset_1 @ X15 @ X14 @ X16) != (X14))
% 0.37/0.58          | ~ (v2_funct_1 @ X16)
% 0.37/0.58          | ((k2_tops_2 @ X15 @ X14 @ X16) = (k2_funct_1 @ X16))
% 0.37/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14)))
% 0.37/0.58          | ~ (v1_funct_2 @ X16 @ X15 @ X14)
% 0.37/0.58          | ~ (v1_funct_1 @ X16))),
% 0.37/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.37/0.58  thf('77', plain,
% 0.37/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58            = (k2_funct_1 @ sk_C))
% 0.37/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58            != (u1_struct_0 @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.58  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('79', plain,
% 0.37/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('81', plain,
% 0.37/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58         = (k2_struct_0 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('82', plain,
% 0.37/0.58      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58          = (k2_funct_1 @ sk_C))
% 0.37/0.58        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.37/0.58      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 0.37/0.58  thf('83', plain,
% 0.37/0.58      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.37/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.37/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58            = (k2_funct_1 @ sk_C)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['74', '82'])).
% 0.37/0.58  thf('84', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('85', plain,
% 0.37/0.58      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.37/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58            = (k2_funct_1 @ sk_C)))),
% 0.37/0.58      inference('demod', [status(thm)], ['83', '84'])).
% 0.37/0.58  thf('86', plain,
% 0.37/0.58      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58         = (k2_funct_1 @ sk_C))),
% 0.37/0.58      inference('simplify', [status(thm)], ['85'])).
% 0.37/0.58  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('88', plain,
% 0.37/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.58         = (k2_struct_0 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('90', plain,
% 0.37/0.58      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.37/0.58        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.37/0.58        | (v2_struct_0 @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)],
% 0.37/0.58                ['70', '71', '72', '73', '86', '87', '88', '89'])).
% 0.37/0.58  thf('91', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_B)
% 0.37/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['90'])).
% 0.37/0.58  thf('92', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('93', plain,
% 0.37/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['91', '92'])).
% 0.37/0.58  thf('94', plain,
% 0.37/0.58      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.37/0.58        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.58        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['67', '93'])).
% 0.37/0.58  thf('95', plain,
% 0.37/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.58        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.37/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['29', '94'])).
% 0.37/0.58  thf('96', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ 
% 0.37/0.58        (k1_zfmisc_1 @ 
% 0.37/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(cc2_relat_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.58  thf('97', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.37/0.58          | (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.58  thf('98', plain,
% 0.37/0.58      ((~ (v1_relat_1 @ 
% 0.37/0.58           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.37/0.58        | (v1_relat_1 @ sk_C))),
% 0.37/0.58      inference('sup-', [status(thm)], ['96', '97'])).
% 0.37/0.58  thf(fc6_relat_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.58  thf('99', plain,
% 0.37/0.58      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.58  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.58      inference('demod', [status(thm)], ['98', '99'])).
% 0.37/0.58  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('102', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('103', plain,
% 0.37/0.58      ((((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.37/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.37/0.58      inference('demod', [status(thm)], ['95', '100', '101', '102'])).
% 0.37/0.58  thf('104', plain,
% 0.37/0.58      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.37/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['28', '103'])).
% 0.37/0.58  thf('105', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('106', plain,
% 0.37/0.58      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.37/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.37/0.58      inference('demod', [status(thm)], ['104', '105'])).
% 0.37/0.58  thf('107', plain,
% 0.37/0.58      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['106'])).
% 0.37/0.58  thf('108', plain,
% 0.37/0.58      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.37/0.58      inference('demod', [status(thm)], ['27', '107'])).
% 0.37/0.58  thf('109', plain,
% 0.37/0.58      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.37/0.58           sk_C)
% 0.37/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.58      inference('sup-', [status(thm)], ['0', '108'])).
% 0.37/0.58  thf('110', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ 
% 0.37/0.58        (k1_zfmisc_1 @ 
% 0.37/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(redefinition_r2_funct_2, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.58         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.58       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.37/0.58  thf('111', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.37/0.58          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 0.37/0.58          | ~ (v1_funct_1 @ X6)
% 0.37/0.58          | ~ (v1_funct_1 @ X9)
% 0.37/0.58          | ~ (v1_funct_2 @ X9 @ X7 @ X8)
% 0.37/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.37/0.58          | (r2_funct_2 @ X7 @ X8 @ X6 @ X9)
% 0.37/0.58          | ((X6) != (X9)))),
% 0.37/0.58      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.37/0.58  thf('112', plain,
% 0.37/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.58         ((r2_funct_2 @ X7 @ X8 @ X9 @ X9)
% 0.37/0.58          | ~ (v1_funct_1 @ X9)
% 0.37/0.58          | ~ (v1_funct_2 @ X9 @ X7 @ X8)
% 0.37/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.37/0.58      inference('simplify', [status(thm)], ['111'])).
% 0.37/0.58  thf('113', plain,
% 0.37/0.58      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.58        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.37/0.58           sk_C))),
% 0.37/0.58      inference('sup-', [status(thm)], ['110', '112'])).
% 0.37/0.58  thf('114', plain,
% 0.37/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('116', plain,
% 0.37/0.58      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.37/0.58      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.37/0.58  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.58      inference('demod', [status(thm)], ['98', '99'])).
% 0.37/0.58  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('120', plain, ($false),
% 0.37/0.58      inference('demod', [status(thm)], ['109', '116', '117', '118', '119'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
