%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.21x35KYUj7

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:24 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  254 (1203 expanded)
%              Number of leaves         :   37 ( 366 expanded)
%              Depth                    :   22
%              Number of atoms          : 2434 (29544 expanded)
%              Number of equality atoms :  141 ( 947 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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

thf('4',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('17',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','15','16'])).

thf('18',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( l1_struct_0 @ X25 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) @ X27 )
       != ( k2_struct_0 @ X25 ) )
      | ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) @ X27 ) )
        = ( k2_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('24',plain,
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
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26','27','28','29','30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X22 @ X24 )
       != X22 )
      | ~ ( v2_funct_1 @ X24 )
      | ( ( k2_tops_2 @ X23 @ X22 @ X24 )
        = ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('42',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('62',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('66',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['50','66'])).

thf('68',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','73','74','75'])).

thf('77',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X22 @ X24 )
       != X22 )
      | ~ ( v2_funct_1 @ X24 )
      | ( ( k2_tops_2 @ X23 @ X22 @ X24 )
        = ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('89',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['91','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('101',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['103','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('114',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90','101','102','114'])).

thf('116',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','73','74','75'])).

thf('118',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('136',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('138',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('144',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['128','129','136','144','145'])).

thf('147',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X22 @ X24 )
       != X22 )
      | ~ ( v2_funct_1 @ X24 )
      | ( ( k2_tops_2 @ X23 @ X22 @ X24 )
        = ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('149',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('151',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('152',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('155',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('160',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X18 ) @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('161',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('164',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162','163','164','165'])).

thf('167',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('169',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['157'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('170',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('171',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('173',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['169','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('178',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['176','177','178','179'])).

thf('181',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('183',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('185',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['180','185'])).

thf('187',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('194',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('195',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['149','158','167','192','195'])).

thf('197',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['119','196'])).

thf('198',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['50','66'])).

thf('201',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','76','118','202'])).

thf('204',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','203'])).

thf('205',plain,(
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

thf('206',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_funct_2 @ X15 @ X16 @ X14 @ X17 )
      | ( X14 != X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('207',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_funct_2 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['205','207'])).

thf('209',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    $false ),
    inference(demod,[status(thm)],['204','211','212','213','214'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.21x35KYUj7
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:28:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.55/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.78  % Solved by: fo/fo7.sh
% 0.55/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.78  % done 581 iterations in 0.308s
% 0.55/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.78  % SZS output start Refutation
% 0.55/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.78  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.55/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.78  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.55/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.78  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.55/0.78  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.55/0.78  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.55/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.78  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.55/0.78  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.55/0.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.78  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.55/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.78  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.55/0.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.55/0.78  thf(t65_funct_1, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.78       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.55/0.78  thf('0', plain,
% 0.55/0.78      (![X10 : $i]:
% 0.55/0.78         (~ (v2_funct_1 @ X10)
% 0.55/0.78          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.55/0.78          | ~ (v1_funct_1 @ X10)
% 0.55/0.78          | ~ (v1_relat_1 @ X10))),
% 0.55/0.78      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.55/0.78  thf(d3_struct_0, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.55/0.78  thf('1', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('2', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('3', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf(t64_tops_2, conjecture,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( l1_struct_0 @ A ) =>
% 0.55/0.78       ( ![B:$i]:
% 0.55/0.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.55/0.78           ( ![C:$i]:
% 0.55/0.78             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.78                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.78                 ( m1_subset_1 @
% 0.55/0.78                   C @ 
% 0.55/0.78                   ( k1_zfmisc_1 @
% 0.55/0.78                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.78               ( ( ( ( k2_relset_1 @
% 0.55/0.78                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.55/0.78                     ( k2_struct_0 @ B ) ) & 
% 0.55/0.78                   ( v2_funct_1 @ C ) ) =>
% 0.55/0.78                 ( r2_funct_2 @
% 0.55/0.78                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.55/0.78                   ( k2_tops_2 @
% 0.55/0.78                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.78                     ( k2_tops_2 @
% 0.55/0.78                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.55/0.78                   C ) ) ) ) ) ) ))).
% 0.55/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.78    (~( ![A:$i]:
% 0.55/0.78        ( ( l1_struct_0 @ A ) =>
% 0.55/0.78          ( ![B:$i]:
% 0.55/0.78            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.55/0.78              ( ![C:$i]:
% 0.55/0.78                ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.78                    ( v1_funct_2 @
% 0.55/0.78                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.78                    ( m1_subset_1 @
% 0.55/0.78                      C @ 
% 0.55/0.78                      ( k1_zfmisc_1 @
% 0.55/0.78                        ( k2_zfmisc_1 @
% 0.55/0.78                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.78                  ( ( ( ( k2_relset_1 @
% 0.55/0.78                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.55/0.78                        ( k2_struct_0 @ B ) ) & 
% 0.55/0.78                      ( v2_funct_1 @ C ) ) =>
% 0.55/0.78                    ( r2_funct_2 @
% 0.55/0.78                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.55/0.78                      ( k2_tops_2 @
% 0.55/0.78                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.78                        ( k2_tops_2 @
% 0.55/0.78                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.55/0.78                      C ) ) ) ) ) ) ) )),
% 0.55/0.78    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.55/0.78  thf('4', plain,
% 0.55/0.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.78          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.78          sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('5', plain,
% 0.55/0.78      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.78           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.78           sk_C)
% 0.55/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup-', [status(thm)], ['3', '4'])).
% 0.55/0.78  thf('6', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('7', plain,
% 0.55/0.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.78          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.78          sk_C)),
% 0.55/0.78      inference('demod', [status(thm)], ['5', '6'])).
% 0.55/0.78  thf('8', plain,
% 0.55/0.78      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.78           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.78           sk_C)
% 0.55/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup-', [status(thm)], ['2', '7'])).
% 0.55/0.78  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('10', plain,
% 0.55/0.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.78          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.78          sk_C)),
% 0.55/0.78      inference('demod', [status(thm)], ['8', '9'])).
% 0.55/0.78  thf('11', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(redefinition_k2_relset_1, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.78       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.55/0.78  thf('12', plain,
% 0.55/0.78      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.55/0.78         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.55/0.78          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.55/0.78      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.78  thf('13', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78         = (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.55/0.78  thf('14', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78         = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('17', plain,
% 0.55/0.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.78          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.55/0.78          sk_C)),
% 0.55/0.78      inference('demod', [status(thm)], ['10', '15', '16'])).
% 0.55/0.78  thf('18', plain,
% 0.55/0.78      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.78           (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.55/0.78           sk_C)
% 0.55/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['1', '17'])).
% 0.55/0.78  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('20', plain,
% 0.55/0.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.78          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.55/0.78          sk_C)),
% 0.55/0.78      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.78  thf(t55_funct_1, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.78       ( ( v2_funct_1 @ A ) =>
% 0.55/0.78         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.55/0.78           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.55/0.78  thf('21', plain,
% 0.55/0.78      (![X8 : $i]:
% 0.55/0.78         (~ (v2_funct_1 @ X8)
% 0.55/0.78          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.55/0.78          | ~ (v1_funct_1 @ X8)
% 0.55/0.78          | ~ (v1_relat_1 @ X8))),
% 0.55/0.78      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.78  thf('22', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(t62_tops_2, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( l1_struct_0 @ A ) =>
% 0.55/0.78       ( ![B:$i]:
% 0.55/0.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.55/0.78           ( ![C:$i]:
% 0.55/0.78             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.78                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.78                 ( m1_subset_1 @
% 0.55/0.78                   C @ 
% 0.55/0.78                   ( k1_zfmisc_1 @
% 0.55/0.78                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.78               ( ( ( ( k2_relset_1 @
% 0.55/0.78                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.55/0.78                     ( k2_struct_0 @ B ) ) & 
% 0.55/0.78                   ( v2_funct_1 @ C ) ) =>
% 0.55/0.78                 ( ( ( k1_relset_1 @
% 0.55/0.78                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.78                       ( k2_tops_2 @
% 0.55/0.78                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.55/0.78                     ( k2_struct_0 @ B ) ) & 
% 0.55/0.78                   ( ( k2_relset_1 @
% 0.55/0.78                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.78                       ( k2_tops_2 @
% 0.55/0.78                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.55/0.78                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.55/0.78  thf('23', plain,
% 0.55/0.78      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.78         ((v2_struct_0 @ X25)
% 0.55/0.78          | ~ (l1_struct_0 @ X25)
% 0.55/0.78          | ((k2_relset_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25) @ X27)
% 0.55/0.78              != (k2_struct_0 @ X25))
% 0.55/0.78          | ~ (v2_funct_1 @ X27)
% 0.55/0.78          | ((k2_relset_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26) @ 
% 0.55/0.78              (k2_tops_2 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25) @ X27))
% 0.55/0.78              = (k2_struct_0 @ X26))
% 0.55/0.78          | ~ (m1_subset_1 @ X27 @ 
% 0.55/0.78               (k1_zfmisc_1 @ 
% 0.55/0.78                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.55/0.78          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.55/0.78          | ~ (v1_funct_1 @ X27)
% 0.55/0.78          | ~ (l1_struct_0 @ X26))),
% 0.55/0.78      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.55/0.78  thf('24', plain,
% 0.55/0.78      ((~ (l1_struct_0 @ sk_A)
% 0.55/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.78            = (k2_struct_0 @ sk_A))
% 0.55/0.78        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78            != (k2_struct_0 @ sk_B))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_B)
% 0.55/0.78        | (v2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.78  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('27', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('28', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('29', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78         = (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.55/0.78  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('32', plain,
% 0.55/0.78      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.78          = (k2_struct_0 @ sk_A))
% 0.55/0.78        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.55/0.78        | (v2_struct_0 @ sk_B))),
% 0.55/0.78      inference('demod', [status(thm)],
% 0.55/0.78                ['24', '25', '26', '27', '28', '29', '30', '31'])).
% 0.55/0.78  thf('33', plain,
% 0.55/0.78      (((v2_struct_0 @ sk_B)
% 0.55/0.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.78            = (k2_struct_0 @ sk_A)))),
% 0.55/0.78      inference('simplify', [status(thm)], ['32'])).
% 0.55/0.78  thf('34', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('35', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(d4_tops_2, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.78       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.55/0.78         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.55/0.78  thf('36', plain,
% 0.55/0.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.55/0.78         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.55/0.78          | ~ (v2_funct_1 @ X24)
% 0.55/0.78          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.55/0.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.55/0.78          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.55/0.78          | ~ (v1_funct_1 @ X24))),
% 0.55/0.78      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.55/0.78  thf('37', plain,
% 0.55/0.78      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.78        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78            = (k2_funct_1 @ sk_C))
% 0.55/0.78        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78            != (u1_struct_0 @ sk_B)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.78  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('39', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('40', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('41', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78         = (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.55/0.78  thf('42', plain,
% 0.55/0.78      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78          = (k2_funct_1 @ sk_C))
% 0.55/0.78        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.55/0.78      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.55/0.78  thf('43', plain,
% 0.55/0.78      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_B)
% 0.55/0.78        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78            = (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['34', '42'])).
% 0.55/0.78  thf('44', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('46', plain,
% 0.55/0.78      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.55/0.78        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78            = (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.55/0.78  thf('47', plain,
% 0.55/0.78      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78         = (k2_funct_1 @ sk_C))),
% 0.55/0.78      inference('simplify', [status(thm)], ['46'])).
% 0.55/0.78  thf('48', plain,
% 0.55/0.78      (((v2_struct_0 @ sk_B)
% 0.55/0.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.55/0.78      inference('demod', [status(thm)], ['33', '47'])).
% 0.55/0.78  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('50', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.55/0.78      inference('clc', [status(thm)], ['48', '49'])).
% 0.55/0.78  thf('51', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('52', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(t31_funct_2, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.78       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.55/0.78         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.55/0.78           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.55/0.78           ( m1_subset_1 @
% 0.55/0.78             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.55/0.78  thf('53', plain,
% 0.55/0.78      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.78         (~ (v2_funct_1 @ X18)
% 0.55/0.78          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.55/0.78          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 0.55/0.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.55/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.55/0.78          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.55/0.78          | ~ (v1_funct_1 @ X18))),
% 0.55/0.78      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.55/0.78  thf('54', plain,
% 0.55/0.78      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.78        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.78           (k1_zfmisc_1 @ 
% 0.55/0.78            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.55/0.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78            != (u1_struct_0 @ sk_B))
% 0.55/0.78        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.78      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.78  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('56', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('57', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78         = (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.55/0.78  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('59', plain,
% 0.55/0.78      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.78         (k1_zfmisc_1 @ 
% 0.55/0.78          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.55/0.78        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.55/0.78      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.55/0.78  thf('60', plain,
% 0.55/0.78      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_B)
% 0.55/0.78        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.78           (k1_zfmisc_1 @ 
% 0.55/0.78            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.55/0.78      inference('sup-', [status(thm)], ['51', '59'])).
% 0.55/0.78  thf('61', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('62', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('63', plain,
% 0.55/0.78      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.55/0.78        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.78           (k1_zfmisc_1 @ 
% 0.55/0.78            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.55/0.78      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.55/0.78  thf('64', plain,
% 0.55/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.78      inference('simplify', [status(thm)], ['63'])).
% 0.55/0.78  thf('65', plain,
% 0.55/0.78      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.55/0.78         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.55/0.78          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.55/0.78      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.78  thf('66', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['64', '65'])).
% 0.55/0.78  thf('67', plain,
% 0.55/0.78      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('sup+', [status(thm)], ['50', '66'])).
% 0.55/0.78  thf('68', plain,
% 0.55/0.78      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.55/0.78        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.78      inference('sup+', [status(thm)], ['21', '67'])).
% 0.55/0.78  thf('69', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(cc2_relat_1, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( v1_relat_1 @ A ) =>
% 0.55/0.78       ( ![B:$i]:
% 0.55/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.55/0.78  thf('70', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.78          | (v1_relat_1 @ X0)
% 0.55/0.78          | ~ (v1_relat_1 @ X1))),
% 0.55/0.78      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.78  thf('71', plain,
% 0.55/0.78      ((~ (v1_relat_1 @ 
% 0.55/0.78           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.55/0.78        | (v1_relat_1 @ sk_C))),
% 0.55/0.78      inference('sup-', [status(thm)], ['69', '70'])).
% 0.55/0.78  thf(fc6_relat_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.55/0.78  thf('72', plain,
% 0.55/0.78      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.55/0.78      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.78  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.78      inference('demod', [status(thm)], ['71', '72'])).
% 0.55/0.78  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('75', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('76', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['68', '73', '74', '75'])).
% 0.55/0.78  thf('77', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('78', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('79', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('80', plain,
% 0.55/0.78      (((m1_subset_1 @ sk_C @ 
% 0.55/0.78         (k1_zfmisc_1 @ 
% 0.55/0.78          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.78      inference('sup+', [status(thm)], ['78', '79'])).
% 0.55/0.78  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('82', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.78      inference('demod', [status(thm)], ['80', '81'])).
% 0.55/0.78  thf('83', plain,
% 0.55/0.78      (((m1_subset_1 @ sk_C @ 
% 0.55/0.78         (k1_zfmisc_1 @ 
% 0.55/0.78          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['77', '82'])).
% 0.55/0.78  thf('84', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('85', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.55/0.78      inference('demod', [status(thm)], ['83', '84'])).
% 0.55/0.78  thf('86', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('87', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.55/0.78      inference('demod', [status(thm)], ['85', '86'])).
% 0.55/0.78  thf('88', plain,
% 0.55/0.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.55/0.78         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.55/0.78          | ~ (v2_funct_1 @ X24)
% 0.55/0.78          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.55/0.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.55/0.78          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.55/0.78          | ~ (v1_funct_1 @ X24))),
% 0.55/0.78      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.55/0.78  thf('89', plain,
% 0.55/0.78      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.55/0.78        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78            = (k2_funct_1 @ sk_C))
% 0.55/0.78        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.78        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78            != (k2_relat_1 @ sk_C)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['87', '88'])).
% 0.55/0.78  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('91', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('92', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('93', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('94', plain,
% 0.55/0.78      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.78      inference('sup+', [status(thm)], ['92', '93'])).
% 0.55/0.78  thf('95', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('96', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.78      inference('demod', [status(thm)], ['94', '95'])).
% 0.55/0.78  thf('97', plain,
% 0.55/0.78      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['91', '96'])).
% 0.55/0.78  thf('98', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('99', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('demod', [status(thm)], ['97', '98'])).
% 0.55/0.78  thf('100', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('101', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.78  thf('102', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('103', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('104', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('105', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78         = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('106', plain,
% 0.55/0.78      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78          = (k2_struct_0 @ sk_B))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.78      inference('sup+', [status(thm)], ['104', '105'])).
% 0.55/0.78  thf('107', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('108', plain,
% 0.55/0.78      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78         = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('demod', [status(thm)], ['106', '107'])).
% 0.55/0.78  thf('109', plain,
% 0.55/0.78      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78          = (k2_struct_0 @ sk_B))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['103', '108'])).
% 0.55/0.78  thf('110', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('111', plain,
% 0.55/0.78      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78         = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('demod', [status(thm)], ['109', '110'])).
% 0.55/0.78  thf('112', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('113', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('114', plain,
% 0.55/0.78      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78         = (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.55/0.78  thf('115', plain,
% 0.55/0.78      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78          = (k2_funct_1 @ sk_C))
% 0.55/0.78        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.55/0.78      inference('demod', [status(thm)], ['89', '90', '101', '102', '114'])).
% 0.55/0.78  thf('116', plain,
% 0.55/0.78      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78         = (k2_funct_1 @ sk_C))),
% 0.55/0.78      inference('simplify', [status(thm)], ['115'])).
% 0.55/0.78  thf('117', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['68', '73', '74', '75'])).
% 0.55/0.78  thf('118', plain,
% 0.55/0.78      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78         = (k2_funct_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['116', '117'])).
% 0.55/0.78  thf('119', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('120', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('121', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('122', plain,
% 0.55/0.78      (((m1_subset_1 @ sk_C @ 
% 0.55/0.78         (k1_zfmisc_1 @ 
% 0.55/0.78          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['120', '121'])).
% 0.55/0.78  thf('123', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('124', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.55/0.78      inference('demod', [status(thm)], ['122', '123'])).
% 0.55/0.78  thf('125', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('126', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.55/0.78      inference('demod', [status(thm)], ['124', '125'])).
% 0.55/0.78  thf('127', plain,
% 0.55/0.78      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.78         (~ (v2_funct_1 @ X18)
% 0.55/0.78          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.55/0.78          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 0.55/0.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.55/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.55/0.78          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.55/0.78          | ~ (v1_funct_1 @ X18))),
% 0.55/0.78      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.55/0.78  thf('128', plain,
% 0.55/0.78      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.55/0.78        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.78           (k1_zfmisc_1 @ 
% 0.55/0.78            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.55/0.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78            != (k2_relat_1 @ sk_C))
% 0.55/0.78        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.78      inference('sup-', [status(thm)], ['126', '127'])).
% 0.55/0.78  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('130', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('131', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('132', plain,
% 0.55/0.78      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['130', '131'])).
% 0.55/0.78  thf('133', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('134', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('demod', [status(thm)], ['132', '133'])).
% 0.55/0.78  thf('135', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('136', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['134', '135'])).
% 0.55/0.78  thf('137', plain,
% 0.55/0.78      (![X21 : $i]:
% 0.55/0.78         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.78  thf('138', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78         = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('139', plain,
% 0.55/0.78      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78          = (k2_struct_0 @ sk_B))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['137', '138'])).
% 0.55/0.78  thf('140', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('141', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.55/0.78         = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('demod', [status(thm)], ['139', '140'])).
% 0.55/0.78  thf('142', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('143', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('144', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78         = (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.55/0.78  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('146', plain,
% 0.55/0.78      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.78         (k1_zfmisc_1 @ 
% 0.55/0.78          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.55/0.78        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.55/0.78      inference('demod', [status(thm)], ['128', '129', '136', '144', '145'])).
% 0.55/0.78  thf('147', plain,
% 0.55/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.78      inference('simplify', [status(thm)], ['146'])).
% 0.55/0.78  thf('148', plain,
% 0.55/0.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.55/0.78         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.55/0.78          | ~ (v2_funct_1 @ X24)
% 0.55/0.78          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.55/0.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.55/0.78          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.55/0.78          | ~ (v1_funct_1 @ X24))),
% 0.55/0.78      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.55/0.78  thf('149', plain,
% 0.55/0.78      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.78        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.55/0.78             (u1_struct_0 @ sk_A))
% 0.55/0.78        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.78        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.78        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['147', '148'])).
% 0.55/0.78  thf('150', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.55/0.78      inference('demod', [status(thm)], ['124', '125'])).
% 0.55/0.78  thf('151', plain,
% 0.55/0.78      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.78         (~ (v2_funct_1 @ X18)
% 0.55/0.78          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.55/0.78          | (v1_funct_1 @ (k2_funct_1 @ X18))
% 0.55/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.55/0.78          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.55/0.78          | ~ (v1_funct_1 @ X18))),
% 0.55/0.78      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.55/0.78  thf('152', plain,
% 0.55/0.78      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.55/0.78        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78            != (k2_relat_1 @ sk_C))
% 0.55/0.78        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.78      inference('sup-', [status(thm)], ['150', '151'])).
% 0.55/0.78  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('154', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['134', '135'])).
% 0.55/0.78  thf('155', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78         = (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.55/0.78  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('157', plain,
% 0.55/0.78      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.78        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.55/0.78      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 0.55/0.78  thf('158', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.78      inference('simplify', [status(thm)], ['157'])).
% 0.55/0.78  thf('159', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.55/0.78      inference('demod', [status(thm)], ['124', '125'])).
% 0.55/0.78  thf('160', plain,
% 0.55/0.78      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.78         (~ (v2_funct_1 @ X18)
% 0.55/0.78          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.55/0.78          | (v1_funct_2 @ (k2_funct_1 @ X18) @ X19 @ X20)
% 0.55/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.55/0.78          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.55/0.78          | ~ (v1_funct_1 @ X18))),
% 0.55/0.78      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.55/0.78  thf('161', plain,
% 0.55/0.78      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.55/0.78        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.55/0.78           (u1_struct_0 @ sk_A))
% 0.55/0.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78            != (k2_relat_1 @ sk_C))
% 0.55/0.78        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.78      inference('sup-', [status(thm)], ['159', '160'])).
% 0.55/0.78  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('163', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['134', '135'])).
% 0.55/0.78  thf('164', plain,
% 0.55/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.78         = (k2_relat_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.55/0.78  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('166', plain,
% 0.55/0.78      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.55/0.78         (u1_struct_0 @ sk_A))
% 0.55/0.78        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.55/0.78      inference('demod', [status(thm)], ['161', '162', '163', '164', '165'])).
% 0.55/0.78  thf('167', plain,
% 0.55/0.78      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.55/0.78        (u1_struct_0 @ sk_A))),
% 0.55/0.78      inference('simplify', [status(thm)], ['166'])).
% 0.55/0.78  thf('168', plain,
% 0.55/0.78      (![X8 : $i]:
% 0.55/0.78         (~ (v2_funct_1 @ X8)
% 0.55/0.78          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 0.55/0.78          | ~ (v1_funct_1 @ X8)
% 0.55/0.78          | ~ (v1_relat_1 @ X8))),
% 0.55/0.78      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.78  thf('169', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.78      inference('simplify', [status(thm)], ['157'])).
% 0.55/0.78  thf(t61_funct_1, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.78       ( ( v2_funct_1 @ A ) =>
% 0.55/0.78         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.55/0.78             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.55/0.78           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.55/0.78             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.55/0.78  thf('170', plain,
% 0.55/0.78      (![X9 : $i]:
% 0.55/0.78         (~ (v2_funct_1 @ X9)
% 0.55/0.78          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 0.55/0.78              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 0.55/0.78          | ~ (v1_funct_1 @ X9)
% 0.55/0.78          | ~ (v1_relat_1 @ X9))),
% 0.55/0.78      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.55/0.78  thf(t48_funct_1, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.78       ( ![B:$i]:
% 0.55/0.78         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.78           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.55/0.78               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.55/0.78             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.55/0.78  thf('171', plain,
% 0.55/0.78      (![X6 : $i, X7 : $i]:
% 0.55/0.78         (~ (v1_relat_1 @ X6)
% 0.55/0.78          | ~ (v1_funct_1 @ X6)
% 0.55/0.78          | (v2_funct_1 @ X7)
% 0.55/0.78          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.55/0.78          | ~ (v2_funct_1 @ (k5_relat_1 @ X6 @ X7))
% 0.55/0.78          | ~ (v1_funct_1 @ X7)
% 0.55/0.78          | ~ (v1_relat_1 @ X7))),
% 0.55/0.78      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.55/0.78  thf('172', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         (~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.55/0.78          | ~ (v1_relat_1 @ X0)
% 0.55/0.78          | ~ (v1_funct_1 @ X0)
% 0.55/0.78          | ~ (v2_funct_1 @ X0)
% 0.55/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.78          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.55/0.78          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.78          | ~ (v1_funct_1 @ X0)
% 0.55/0.78          | ~ (v1_relat_1 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['170', '171'])).
% 0.55/0.78  thf(fc4_funct_1, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.55/0.78       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.55/0.78  thf('173', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 0.55/0.78      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.55/0.78  thf('174', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         (~ (v1_relat_1 @ X0)
% 0.55/0.78          | ~ (v1_funct_1 @ X0)
% 0.55/0.78          | ~ (v2_funct_1 @ X0)
% 0.55/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.78          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.55/0.78          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.78          | ~ (v1_funct_1 @ X0)
% 0.55/0.78          | ~ (v1_relat_1 @ X0))),
% 0.55/0.78      inference('demod', [status(thm)], ['172', '173'])).
% 0.55/0.78  thf('175', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.78          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.55/0.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.78          | ~ (v2_funct_1 @ X0)
% 0.55/0.78          | ~ (v1_funct_1 @ X0)
% 0.55/0.78          | ~ (v1_relat_1 @ X0))),
% 0.55/0.78      inference('simplify', [status(thm)], ['174'])).
% 0.55/0.78  thf('176', plain,
% 0.55/0.78      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.78        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.78        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['169', '175'])).
% 0.55/0.78  thf('177', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.78      inference('demod', [status(thm)], ['71', '72'])).
% 0.55/0.78  thf('178', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('179', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('180', plain,
% 0.55/0.78      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.78        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.78        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('demod', [status(thm)], ['176', '177', '178', '179'])).
% 0.55/0.78  thf('181', plain,
% 0.55/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.78      inference('simplify', [status(thm)], ['146'])).
% 0.55/0.78  thf('182', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.78          | (v1_relat_1 @ X0)
% 0.55/0.78          | ~ (v1_relat_1 @ X1))),
% 0.55/0.78      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.78  thf('183', plain,
% 0.55/0.78      ((~ (v1_relat_1 @ 
% 0.55/0.78           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))
% 0.55/0.78        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['181', '182'])).
% 0.55/0.78  thf('184', plain,
% 0.55/0.78      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.55/0.78      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.78  thf('185', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['183', '184'])).
% 0.55/0.78  thf('186', plain,
% 0.55/0.78      ((((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.78        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('demod', [status(thm)], ['180', '185'])).
% 0.55/0.78  thf('187', plain,
% 0.55/0.78      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.55/0.78        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.78        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['168', '186'])).
% 0.55/0.78  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.78      inference('demod', [status(thm)], ['71', '72'])).
% 0.55/0.78  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('191', plain,
% 0.55/0.78      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.55/0.78        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 0.55/0.78  thf('192', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.78      inference('simplify', [status(thm)], ['191'])).
% 0.55/0.78  thf('193', plain,
% 0.55/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.78      inference('simplify', [status(thm)], ['146'])).
% 0.55/0.78  thf('194', plain,
% 0.55/0.78      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.55/0.78         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.55/0.78          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.55/0.78      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.78  thf('195', plain,
% 0.55/0.78      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['193', '194'])).
% 0.55/0.78  thf('196', plain,
% 0.55/0.78      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.78        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('demod', [status(thm)], ['149', '158', '167', '192', '195'])).
% 0.55/0.78  thf('197', plain,
% 0.55/0.78      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_A)
% 0.55/0.78        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.78      inference('sup-', [status(thm)], ['119', '196'])).
% 0.55/0.78  thf('198', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('199', plain,
% 0.55/0.78      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.55/0.78        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.78      inference('demod', [status(thm)], ['197', '198'])).
% 0.55/0.78  thf('200', plain,
% 0.55/0.78      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('sup+', [status(thm)], ['50', '66'])).
% 0.55/0.78  thf('201', plain,
% 0.55/0.78      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.55/0.78        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.78      inference('demod', [status(thm)], ['199', '200'])).
% 0.55/0.78  thf('202', plain,
% 0.55/0.78      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.78         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.78      inference('simplify', [status(thm)], ['201'])).
% 0.55/0.78  thf('203', plain,
% 0.55/0.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.78          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.55/0.78      inference('demod', [status(thm)], ['20', '76', '118', '202'])).
% 0.55/0.78  thf('204', plain,
% 0.55/0.78      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.78           sk_C)
% 0.55/0.78        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.78      inference('sup-', [status(thm)], ['0', '203'])).
% 0.55/0.78  thf('205', plain,
% 0.55/0.78      ((m1_subset_1 @ sk_C @ 
% 0.55/0.78        (k1_zfmisc_1 @ 
% 0.55/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(redefinition_r2_funct_2, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.78         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.55/0.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.78       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.55/0.78  thf('206', plain,
% 0.55/0.78      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.55/0.78         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.55/0.78          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.55/0.78          | ~ (v1_funct_1 @ X14)
% 0.55/0.78          | ~ (v1_funct_1 @ X17)
% 0.55/0.78          | ~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.55/0.78          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.55/0.78          | (r2_funct_2 @ X15 @ X16 @ X14 @ X17)
% 0.55/0.78          | ((X14) != (X17)))),
% 0.55/0.78      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.55/0.78  thf('207', plain,
% 0.55/0.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.55/0.78         ((r2_funct_2 @ X15 @ X16 @ X17 @ X17)
% 0.55/0.78          | ~ (v1_funct_1 @ X17)
% 0.55/0.78          | ~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.55/0.78          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.55/0.78      inference('simplify', [status(thm)], ['206'])).
% 0.55/0.78  thf('208', plain,
% 0.55/0.78      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.78        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.78           sk_C))),
% 0.55/0.78      inference('sup-', [status(thm)], ['205', '207'])).
% 0.55/0.78  thf('209', plain,
% 0.55/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('210', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('211', plain,
% 0.55/0.78      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.55/0.78      inference('demod', [status(thm)], ['208', '209', '210'])).
% 0.55/0.78  thf('212', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.78      inference('demod', [status(thm)], ['71', '72'])).
% 0.55/0.78  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('214', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('215', plain, ($false),
% 0.55/0.78      inference('demod', [status(thm)], ['204', '211', '212', '213', '214'])).
% 0.55/0.78  
% 0.55/0.78  % SZS output end Refutation
% 0.55/0.78  
% 0.55/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
