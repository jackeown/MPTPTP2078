%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xTfpQPWXTX

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:12 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 379 expanded)
%              Number of leaves         :   28 ( 124 expanded)
%              Depth                    :   21
%              Number of atoms          : 1497 (9433 expanded)
%              Number of equality atoms :   73 ( 281 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
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

thf('3',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
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

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','19','20','25'])).

thf('27',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','27'])).

thf('29',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('36',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('39',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['26'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
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

thf('43',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
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

thf('52',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','48','61'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('69',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['26'])).

thf('70',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
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

thf('73',plain,(
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

thf('74',plain,
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
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['60'])).

thf('79',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75','76','77','78','79','80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['71','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','70','88'])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('92',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['90','93','94','95'])).

thf('97',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['31','100'])).

thf('102',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','101'])).

thf('103',plain,(
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

thf('104',plain,(
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

thf('105',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_funct_2 @ X6 @ X7 @ X8 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['91','92'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['102','109','110','111','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xTfpQPWXTX
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 317 iterations in 0.141s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.60  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.40/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.60  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.40/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.60  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.40/0.60  thf(t65_funct_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.60       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      (![X1 : $i]:
% 0.40/0.60         (~ (v2_funct_1 @ X1)
% 0.40/0.60          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.40/0.60          | ~ (v1_funct_1 @ X1)
% 0.40/0.60          | ~ (v1_relat_1 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.40/0.60  thf(d3_struct_0, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (![X9 : $i]:
% 0.40/0.60         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X9 : $i]:
% 0.40/0.60         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.60  thf(t64_tops_2, conjecture,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_struct_0 @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.40/0.60           ( ![C:$i]:
% 0.40/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.60                 ( m1_subset_1 @
% 0.40/0.60                   C @ 
% 0.40/0.60                   ( k1_zfmisc_1 @
% 0.40/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.60               ( ( ( ( k2_relset_1 @
% 0.40/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.60                   ( v2_funct_1 @ C ) ) =>
% 0.40/0.60                 ( r2_funct_2 @
% 0.40/0.60                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.60                   ( k2_tops_2 @
% 0.40/0.60                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.60                     ( k2_tops_2 @
% 0.40/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.40/0.60                   C ) ) ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i]:
% 0.40/0.60        ( ( l1_struct_0 @ A ) =>
% 0.40/0.60          ( ![B:$i]:
% 0.40/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.40/0.60              ( ![C:$i]:
% 0.40/0.60                ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.60                    ( v1_funct_2 @
% 0.40/0.60                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.60                    ( m1_subset_1 @
% 0.40/0.60                      C @ 
% 0.40/0.60                      ( k1_zfmisc_1 @
% 0.40/0.60                        ( k2_zfmisc_1 @
% 0.40/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.60                  ( ( ( ( k2_relset_1 @
% 0.40/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.60                        ( k2_struct_0 @ B ) ) & 
% 0.40/0.60                      ( v2_funct_1 @ C ) ) =>
% 0.40/0.60                    ( r2_funct_2 @
% 0.40/0.60                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.60                      ( k2_tops_2 @
% 0.40/0.60                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.60                        ( k2_tops_2 @
% 0.40/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.40/0.60                      C ) ) ) ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.60          sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.60           sk_C)
% 0.40/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.60  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.60          sk_C)),
% 0.40/0.60      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X9 : $i]:
% 0.40/0.60         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (((m1_subset_1 @ sk_C @ 
% 0.40/0.60         (k1_zfmisc_1 @ 
% 0.40/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.40/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.40/0.60  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('11', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.40/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.60  thf(d4_tops_2, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.60       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.40/0.60         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.60         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.40/0.60          | ~ (v2_funct_1 @ X12)
% 0.40/0.60          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.40/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.40/0.60          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.40/0.60          | ~ (v1_funct_1 @ X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60            = (k2_funct_1 @ sk_C))
% 0.40/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60            != (k2_struct_0 @ sk_B)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.60  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (![X9 : $i]:
% 0.40/0.60         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.60      inference('sup+', [status(thm)], ['15', '16'])).
% 0.40/0.60  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.60  thf('20', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      (![X9 : $i]:
% 0.40/0.60         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60         = (k2_struct_0 @ sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60          = (k2_struct_0 @ sk_B))
% 0.40/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.60      inference('sup+', [status(thm)], ['21', '22'])).
% 0.40/0.60  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60         = (k2_struct_0 @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60          = (k2_funct_1 @ sk_C))
% 0.40/0.60        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['13', '14', '19', '20', '25'])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60         = (k2_funct_1 @ sk_C))),
% 0.40/0.60      inference('simplify', [status(thm)], ['26'])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60           (k2_funct_1 @ sk_C)) @ 
% 0.40/0.60          sk_C)),
% 0.40/0.60      inference('demod', [status(thm)], ['6', '27'])).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.60           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60            (k2_funct_1 @ sk_C)) @ 
% 0.40/0.60           sk_C)
% 0.40/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '28'])).
% 0.40/0.60  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.60          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60           (k2_funct_1 @ sk_C)) @ 
% 0.40/0.60          sk_C)),
% 0.40/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      (![X9 : $i]:
% 0.40/0.60         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.60  thf(t62_funct_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.60       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v2_funct_1 @ X0)
% 0.40/0.60          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t62_funct_1])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.40/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.60  thf(dt_k2_tops_2, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.60       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.40/0.60         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.40/0.60         ( m1_subset_1 @
% 0.40/0.60           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.40/0.60           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.60         ((m1_subset_1 @ (k2_tops_2 @ X13 @ X14 @ X15) @ 
% 0.40/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13)))
% 0.40/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.40/0.60          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.40/0.60          | ~ (v1_funct_1 @ X15))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.60        | (m1_subset_1 @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60           (k1_zfmisc_1 @ 
% 0.40/0.60            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.60  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      ((m1_subset_1 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.40/0.60  thf('40', plain,
% 0.40/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60         = (k2_funct_1 @ sk_C))),
% 0.40/0.60      inference('simplify', [status(thm)], ['26'])).
% 0.40/0.60  thf('41', plain,
% 0.40/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.40/0.60  thf('42', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.60         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.40/0.60          | ~ (v2_funct_1 @ X12)
% 0.40/0.60          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.40/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.40/0.60          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.40/0.60          | ~ (v1_funct_1 @ X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.60        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.40/0.60             (u1_struct_0 @ sk_A))
% 0.40/0.60        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.60        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.40/0.60  thf('44', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('45', plain,
% 0.40/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.60         ((v1_funct_1 @ (k2_tops_2 @ X13 @ X14 @ X15))
% 0.40/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.40/0.60          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.40/0.60          | ~ (v1_funct_1 @ X15))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.60  thf('46', plain,
% 0.40/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.60        | (v1_funct_1 @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.60  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('48', plain,
% 0.40/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('49', plain,
% 0.40/0.60      (![X9 : $i]:
% 0.40/0.60         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.60  thf('50', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('51', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.60         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.40/0.60          | ~ (v2_funct_1 @ X12)
% 0.40/0.60          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.40/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.40/0.60          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.40/0.60          | ~ (v1_funct_1 @ X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.40/0.60  thf('52', plain,
% 0.40/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60            = (k2_funct_1 @ sk_C))
% 0.40/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60            != (u1_struct_0 @ sk_B)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.60  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('54', plain,
% 0.40/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('55', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('56', plain,
% 0.40/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60         = (k2_struct_0 @ sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('57', plain,
% 0.40/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60          = (k2_funct_1 @ sk_C))
% 0.40/0.60        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.40/0.60  thf('58', plain,
% 0.40/0.60      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.40/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60            = (k2_funct_1 @ sk_C)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['49', '57'])).
% 0.40/0.60  thf('59', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('60', plain,
% 0.40/0.60      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60            = (k2_funct_1 @ sk_C)))),
% 0.40/0.60      inference('demod', [status(thm)], ['58', '59'])).
% 0.40/0.60  thf('61', plain,
% 0.40/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60         = (k2_funct_1 @ sk_C))),
% 0.40/0.60      inference('simplify', [status(thm)], ['60'])).
% 0.40/0.60  thf('62', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.60      inference('demod', [status(thm)], ['46', '47', '48', '61'])).
% 0.40/0.60  thf('63', plain,
% 0.40/0.60      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.40/0.60           (u1_struct_0 @ sk_A))
% 0.40/0.60        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.60        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('demod', [status(thm)], ['43', '62'])).
% 0.40/0.60  thf('64', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.40/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.60  thf('65', plain,
% 0.40/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.60         ((v1_funct_2 @ (k2_tops_2 @ X13 @ X14 @ X15) @ X14 @ X13)
% 0.40/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.40/0.60          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.40/0.60          | ~ (v1_funct_1 @ X15))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.60  thf('66', plain,
% 0.40/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.60        | (v1_funct_2 @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60           (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.60  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('68', plain,
% 0.40/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.60  thf('69', plain,
% 0.40/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60         = (k2_funct_1 @ sk_C))),
% 0.40/0.60      inference('simplify', [status(thm)], ['26'])).
% 0.40/0.60  thf('70', plain,
% 0.40/0.60      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.40/0.60        (u1_struct_0 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.40/0.60  thf('71', plain,
% 0.40/0.60      (![X9 : $i]:
% 0.40/0.60         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.60  thf('72', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t62_tops_2, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_struct_0 @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.40/0.60           ( ![C:$i]:
% 0.40/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.60                 ( m1_subset_1 @
% 0.40/0.60                   C @ 
% 0.40/0.60                   ( k1_zfmisc_1 @
% 0.40/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.60               ( ( ( ( k2_relset_1 @
% 0.40/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.60                   ( v2_funct_1 @ C ) ) =>
% 0.40/0.60                 ( ( ( k1_relset_1 @
% 0.40/0.60                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.60                       ( k2_tops_2 @
% 0.40/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.40/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.60                   ( ( k2_relset_1 @
% 0.40/0.60                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.60                       ( k2_tops_2 @
% 0.40/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.40/0.60                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.40/0.60  thf('73', plain,
% 0.40/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.60         ((v2_struct_0 @ X16)
% 0.40/0.60          | ~ (l1_struct_0 @ X16)
% 0.40/0.60          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.40/0.60              != (k2_struct_0 @ X16))
% 0.40/0.60          | ~ (v2_funct_1 @ X18)
% 0.40/0.60          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.40/0.60              (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.40/0.60              = (k2_struct_0 @ X17))
% 0.40/0.60          | ~ (m1_subset_1 @ X18 @ 
% 0.40/0.60               (k1_zfmisc_1 @ 
% 0.40/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.40/0.60          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.40/0.60          | ~ (v1_funct_1 @ X18)
% 0.40/0.60          | ~ (l1_struct_0 @ X17))),
% 0.40/0.60      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.40/0.60  thf('74', plain,
% 0.40/0.60      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.60            = (k2_struct_0 @ sk_A))
% 0.40/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60            != (k2_struct_0 @ sk_B))
% 0.40/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.44/0.60        | (v2_struct_0 @ sk_B))),
% 0.44/0.60      inference('sup-', [status(thm)], ['72', '73'])).
% 0.44/0.60  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('77', plain,
% 0.44/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('78', plain,
% 0.44/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.44/0.60         = (k2_funct_1 @ sk_C))),
% 0.44/0.60      inference('simplify', [status(thm)], ['60'])).
% 0.44/0.60  thf('79', plain, ((v2_funct_1 @ sk_C)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('80', plain,
% 0.44/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.44/0.60         = (k2_struct_0 @ sk_B))),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('82', plain,
% 0.44/0.60      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.60          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.44/0.60        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.44/0.60        | (v2_struct_0 @ sk_B))),
% 0.44/0.60      inference('demod', [status(thm)],
% 0.44/0.60                ['74', '75', '76', '77', '78', '79', '80', '81'])).
% 0.44/0.60  thf('83', plain,
% 0.44/0.60      (((v2_struct_0 @ sk_B)
% 0.44/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.60            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.44/0.60      inference('simplify', [status(thm)], ['82'])).
% 0.44/0.60  thf('84', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('85', plain,
% 0.44/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.60         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.44/0.60      inference('clc', [status(thm)], ['83', '84'])).
% 0.44/0.60  thf('86', plain,
% 0.44/0.60      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.60          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.44/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.44/0.60      inference('sup+', [status(thm)], ['71', '85'])).
% 0.44/0.60  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('88', plain,
% 0.44/0.60      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.60         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.44/0.60      inference('demod', [status(thm)], ['86', '87'])).
% 0.44/0.60  thf('89', plain,
% 0.44/0.60      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.60          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.44/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.44/0.60        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.44/0.60      inference('demod', [status(thm)], ['63', '70', '88'])).
% 0.44/0.60  thf('90', plain,
% 0.44/0.60      ((~ (v1_relat_1 @ sk_C)
% 0.44/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.44/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.44/0.60        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.44/0.60        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.60            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.44/0.60      inference('sup-', [status(thm)], ['33', '89'])).
% 0.44/0.60  thf('91', plain,
% 0.44/0.60      ((m1_subset_1 @ sk_C @ 
% 0.44/0.60        (k1_zfmisc_1 @ 
% 0.44/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf(cc1_relset_1, axiom,
% 0.44/0.60    (![A:$i,B:$i,C:$i]:
% 0.44/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.60       ( v1_relat_1 @ C ) ))).
% 0.44/0.60  thf('92', plain,
% 0.44/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.60         ((v1_relat_1 @ X2)
% 0.44/0.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.44/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.60  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.60      inference('sup-', [status(thm)], ['91', '92'])).
% 0.44/0.60  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('96', plain,
% 0.44/0.60      ((((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.44/0.60        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.60            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.44/0.60      inference('demod', [status(thm)], ['90', '93', '94', '95'])).
% 0.44/0.60  thf('97', plain,
% 0.44/0.60      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.44/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.44/0.60        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.60            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.44/0.60      inference('sup-', [status(thm)], ['32', '96'])).
% 0.44/0.60  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('99', plain,
% 0.44/0.60      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.44/0.60        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.60            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.44/0.60      inference('demod', [status(thm)], ['97', '98'])).
% 0.44/0.60  thf('100', plain,
% 0.44/0.60      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.60         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.44/0.60      inference('simplify', [status(thm)], ['99'])).
% 0.44/0.60  thf('101', plain,
% 0.44/0.60      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.60          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.44/0.60      inference('demod', [status(thm)], ['31', '100'])).
% 0.44/0.60  thf('102', plain,
% 0.44/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.44/0.60           sk_C)
% 0.44/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.44/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.44/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.44/0.60      inference('sup-', [status(thm)], ['0', '101'])).
% 0.44/0.60  thf('103', plain,
% 0.44/0.60      ((m1_subset_1 @ sk_C @ 
% 0.44/0.60        (k1_zfmisc_1 @ 
% 0.44/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf(redefinition_r2_funct_2, axiom,
% 0.44/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.44/0.60         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.60       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.44/0.60  thf('104', plain,
% 0.44/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.60         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.44/0.60          | ~ (v1_funct_2 @ X5 @ X6 @ X7)
% 0.44/0.60          | ~ (v1_funct_1 @ X5)
% 0.44/0.60          | ~ (v1_funct_1 @ X8)
% 0.44/0.60          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.44/0.60          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.44/0.60          | (r2_funct_2 @ X6 @ X7 @ X5 @ X8)
% 0.44/0.60          | ((X5) != (X8)))),
% 0.44/0.60      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.44/0.60  thf('105', plain,
% 0.44/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.60         ((r2_funct_2 @ X6 @ X7 @ X8 @ X8)
% 0.44/0.60          | ~ (v1_funct_1 @ X8)
% 0.44/0.60          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.44/0.60          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.44/0.60      inference('simplify', [status(thm)], ['104'])).
% 0.44/0.60  thf('106', plain,
% 0.44/0.60      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.44/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.44/0.60        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.44/0.60           sk_C))),
% 0.44/0.60      inference('sup-', [status(thm)], ['103', '105'])).
% 0.44/0.60  thf('107', plain,
% 0.44/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('109', plain,
% 0.44/0.60      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.44/0.60      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.44/0.60  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.60      inference('sup-', [status(thm)], ['91', '92'])).
% 0.44/0.60  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('113', plain, ($false),
% 0.44/0.60      inference('demod', [status(thm)], ['102', '109', '110', '111', '112'])).
% 0.44/0.60  
% 0.44/0.60  % SZS output end Refutation
% 0.44/0.60  
% 0.44/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
